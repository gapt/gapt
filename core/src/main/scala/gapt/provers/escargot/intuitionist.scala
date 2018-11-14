package gapt.provers.escargot

import ammonite.ops.FilePath
import gapt.expr._
import gapt.expr.fol.folSubTerms
import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.formats.tptp.{ TptpImporter, sequentProofToTptp }
import gapt.proofs.expansion.{ ETAnd, ETAtom, ETBottom, ETDefinition, ETImp, ETMerge, ETNeg, ETOr, ETSkolemQuantifier, ETStrongQuantifier, ETTop, ETWeakQuantifier, ETWeakening, ExpansionProof, ExpansionProofToLK, ExpansionProofToMG3i, ExpansionProofToMG3iViaSAT, ExpansionSequent, ExpansionTree, deskolemizeET, formulaToExpansionTree }
import gapt.proofs.lk.{ LKProof, MG3iToLJ, isMaeharaMG3i, normalizeLKt }
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.prooftool.LKProofViewer
import gapt.provers.{ OneShotProver, Prover }
import gapt.provers.congruence.SimpleSmtSolver
import gapt.provers.eprover.EProver
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire
import gapt.utils.{ LogHandler, Maybe, quiet }

object heuristicDecidabilityInstantiation {
  def apply( proof: ExpansionProof ): ExpansionProof = {
    val terms = folSubTerms( proof.deep.toImplication ).groupBy( _.ty )
    val cands = proof.shallow.antecedent.filter( isCandidate )
    ExpansionProof( ETMerge(
      ( for ( cand <- cands ) yield formulaToExpansionTree(
        cand,
        mkSubsts( boundVariables( cand ), terms ), Polarity.InAntecedent ) ) ++:
        proof.expansionSequent ) )
  }

  def mkSubsts( vars: Set[Var], terms: Map[Ty, Set[Expr]] ): Set[Substitution] = {
    import cats.syntax.traverse._
    import cats.instances.list._
    vars.toList.traverse( v => terms( v.ty ).toList.map( v -> _ ) ).
      map( Substitution( _ ) ).toSet
  }

  def isCandidate: Formula => Boolean = {
    case Imp( lhs, rhs )               => !containsQuantifierOnLogicalLevel( lhs ) && isCandidate( rhs )
    case All( _, rhs )                 => isCandidate( rhs )
    case Or( Neg( a ), a_ ) if a == a_ => !containsQuantifierOnLogicalLevel( a )
    case Or( a, Neg( a_ ) ) if a == a_ => !containsQuantifierOnLogicalLevel( a )
    case _                             => false
  }
}

object pushWeakeningsUp {
  def apply( ep: ExpansionProof ): ExpansionProof = ExpansionProof( apply( ep.expansionSequent ) )
  def apply( es: ExpansionSequent ): ExpansionSequent = es.map( apply )

  def apply( et: ExpansionTree ): ExpansionTree = et match {
    case ETAtom( _, _ ) | ETBottom( _ ) | ETTop( _ ) => et
    case ETWeakening( sh, pol )                      => apply( sh, pol )
    case ETMerge( a, b )                             => ETMerge( apply( a ), apply( b ) )
    case ETNeg( a )                                  => ETNeg( apply( a ) )
    case ETAnd( a, b )                               => ETAnd( apply( a ), apply( b ) )
    case ETOr( a, b )                                => ETOr( apply( a ), apply( b ) )
    case ETImp( a, b )                               => ETImp( apply( a ), apply( b ) )
    case ETWeakQuantifier( sh, insts )               => ETWeakQuantifier( sh, Map() ++ insts.mapValues( apply ) )
    case ETStrongQuantifier( sh, ev, ch )            => ETStrongQuantifier( sh, ev, apply( ch ) )
    case ETSkolemQuantifier( sh, skT, ch )           => ETSkolemQuantifier( sh, skT, apply( ch ) )
    case ETDefinition( sh, ch )                      => ETDefinition( sh, apply( ch ) )
  }

  def apply( sh: Formula, pol: Polarity ): ExpansionTree = sh match {
    case sh: Atom    => ETAtom( sh, pol )
    case Neg( a )    => ETNeg( apply( a, !pol ) )
    case And( a, b ) => ETAnd( apply( a, pol ), apply( b, pol ) )
    case Or( a, b )  => ETOr( apply( a, pol ), apply( b, pol ) )
    case Imp( a, b ) => ETImp( apply( a, !pol ), apply( b, pol ) )
    case _           => ETWeakening( sh, pol )
  }
}

object isEssentiallyCNF {
  private def hypLhs: Formula => Boolean = {
    case _: Atom     => true
    case Bottom()    => true
    case Top()       => true
    case And( f, g ) => hypLhs( f ) && hypLhs( g )
    case Or( f, g )  => hypLhs( f ) && hypLhs( g )
    case Ex( _, f )  => hypLhs( f )
    case _           => false
  }

  private def hypMatrix: Formula => Boolean = {
    case _: Atom     => true
    case Bottom()    => true
    case Top()       => true
    case All( _, f ) => hypMatrix( f )
    case Imp( f, g ) => hypLhs( f ) && hypMatrix( g )
    case Neg( f )    => hypLhs( f )
    case And( f, g ) => hypMatrix( f ) && hypMatrix( g )
    case Or( f, g )  => hypMatrix( f ) && hypMatrix( g )
    case _           => false
  }

  private def prenexHyp: Formula => Boolean = {
    case All( _, f ) => prenexHyp( f )
    case Ex( _, f )  => prenexHyp( f )
    case And( f, g ) => prenexHyp( f ) && prenexHyp( g )
    case Or( f, g )  => prenexHyp( f ) && prenexHyp( g )
    case f           => hypMatrix( f )
  }

  private def fml: Formula => Boolean = {
    case Imp( f, g ) => prenexHyp( f ) && fml( g )
    case And( f, g ) => fml( f ) && fml( g )
    case All( _, f ) => fml( f )
    case f           => hypLhs( f )
  }

  def apply( formula: Formula ): Boolean = fml( formula )
  def apply( sequent: HOLSequent ): Boolean = apply( sequent.toImplication )
}

class IEscargot(
    backend:         Prover        = Escargot,
    method:          ExpToLKMethod = ExpToLKMethod.MG3iViaSAT,
    showInProoftool: Boolean       = false,
    convertToLJ:     Boolean       = false,
    filename:        String        = "" ) extends OneShotProver {
  def expansionProofToMG3i( expProofWithSk: ExpansionProof )( implicit ctx: Context ): Option[LKProof] = {
    val deskExpProof = deskolemizeET( expProofWithSk )
    EscargotLogger.info( "converting expansion proof to LK" )
    quiet( method.convert( deskExpProof ) ) match {
      case Right( lk0 ) =>
        val lk = if ( !convertToLJ ) lk0 else normalizeLKt.lk( MG3iToLJ( lk0 ) )
        EscargotLogger.info( s"LK proof has ${lk.dagLike.size} inferences" )
        val maxSuccSize = lk.subProofs.map( _.endSequent.succedent.toSet.size ).max
        EscargotLogger.info( s"LK proof has maximum succedent size $maxSuccSize" )
        val inMG3i = isMaeharaMG3i( lk )
        EscargotLogger.info( s"LK proof is in mG3i: $inMG3i" )
        if ( showInProoftool ) {
          val viewer = new LKProofViewer( filename, lk )
          viewer.markNonIntuitionisticInferences()
          viewer.showFrame()
        }
        if ( inMG3i ) Some( lk ) else None
      case Left( unprovable ) =>
        EscargotLogger.info( s"stuck at: $unprovable" )
        None
    }
  }

  def getLKProof( seq: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[LKProof] =
    getLKProof_( seq ) match {
      case Some( Right( proof ) ) => Some( proof )
      case _                      => None
    }

  def getLKProof_( seq: HOLSequent )( implicit ctx0: Maybe[MutableContext] ): Option[Either[Unit, LKProof]] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( seq ) )

    val essentiallyCNF = isEssentiallyCNF( seq )
    if ( essentiallyCNF )
      EscargotLogger.info( "problem is essentially in clause normal form" )

    if ( !containsQuantifierOnLogicalLevel( seq.toImplication ) ) {
      if ( !SimpleSmtSolver.isValid( seq ) ) Some( Left( () ) )
      else {
        if ( essentiallyCNF ) EscargotLogger.info( "SZS status Theorem" )
        expansionProofToMG3i( ExpansionProof( formulaToExpansionTree( seq ) ) ) match {
          case Some( lk ) => Some( Right( lk ) )
          case None       => if ( method.isComplete ) Some( Left( () ) ) else None
        }
      }
    } else {
      quiet( backend.getExpansionProof( seq ) ) match {
        case Some( expansion0 ) =>
          EscargotLogger.info( "found classical expansion proof" )
          val proofEssentiallyCNF = essentiallyCNF || isEssentiallyCNF( expansion0.shallow )
          if ( !essentiallyCNF && proofEssentiallyCNF )
            EscargotLogger.info( "axioms used by proof are essentially in clause normal form" )
          if ( proofEssentiallyCNF )
            EscargotLogger.info( "SZS status Theorem" )
          val expansion1 = ETWeakening( expansion0, seq )
          val expansion2 = pushWeakeningsUp( expansion1 )
          val expansion3 = heuristicDecidabilityInstantiation( expansion2 )
          expansionProofToMG3i( expansion3 ) match {
            case Some( lk ) =>
              require( lk.endSequent.isSubsetOf( seq ) )
              Some( Right( lk ) )
            case None =>
              EscargotLogger.info( "constructivization failed" )
              None
          }
        case None =>
          Some( Left( () ) )
      }
    }
  }
}

sealed trait ExpToLKMethod {
  def isComplete: Boolean = false
  def convert( exp: ExpansionProof )( implicit ctx: Context ): Either[HOLSequent, LKProof]
}
object ExpToLKMethod {
  case object MG3iViaSAT extends ExpToLKMethod {
    override def isComplete = true
    def convert( exp: ExpansionProof )( implicit ctx: Context ): Either[HOLSequent, LKProof] =
      ExpansionProofToMG3iViaSAT( exp ).left.map( _._2 )
  }
  case object MG4ip extends ExpToLKMethod {
    def convert( exp: ExpansionProof )( implicit ctx: Context ): Either[HOLSequent, LKProof] =
      ExpansionProofToMG3i( exp ).left.map {
        case ( th, seq ) => ( th.getExpansionTrees ++: seq ).shallow
      }
  }
  case object Heuristic extends ExpToLKMethod {
    def convert( exp: ExpansionProof )( implicit ctx: Context ): Either[HOLSequent, LKProof] =
      ExpansionProofToLK.withIntuitionisticHeuristics( exp ).left.map {
        case ( th, seq ) => ( th.getExpansionTrees ++: seq ).shallow
      }
  }
}

object IEscargot extends IEscargot(
  backend = Escargot,
  method = ExpToLKMethod.MG3iViaSAT,
  convertToLJ = false,
  showInProoftool = false,
  filename = "" ) {
  import ExpToLKMethod._

  case class Options(
      verbose:   Boolean       = false,
      backend:   Prover        = Escargot,
      prooftool: Boolean       = false,
      convertLJ: Boolean       = false,
      method:    ExpToLKMethod = MG3iViaSAT,
      files:     Seq[String]   = Seq() ) {
    def parse( args: List[String] ): Either[String, Options] =
      args match {
        case "--backend=vampire" :: rest       => copy( backend = Vampire ).parse( rest )
        case "--backend=spass" :: rest         => copy( backend = SPASS ).parse( rest )
        case "--backend=escargot" :: rest      => copy( backend = Escargot ).parse( rest )
        case "--backend=e" :: rest             => copy( backend = new EProver( extraArgs = Seq( "--auto" ) ) ).parse( rest )
        case "--lj" :: rest                    => copy( convertLJ = true ).parse( rest )
        case "--prooftool" :: rest             => copy( prooftool = true ).parse( rest )
        case "--heuristic" :: rest             => copy( method = Heuristic ).parse( rest )
        case "--mg4ip" :: rest                 => copy( method = MG4ip ).parse( rest )
        case "--mg3isat" :: rest               => copy( method = MG3iViaSAT ).parse( rest )
        case "-v" :: rest                      => copy( verbose = true ).parse( rest )
        case opt :: _ if opt.startsWith( "-" ) => Left( s"unknown option $opt" )
        case file :: rest                      => copy( files = files :+ file ).parse( rest )
        case Nil                               => Right( this )
      }
  }

  def main( args: Array[String] ): Unit = {
    LogHandler.current.value = LogHandler.tstp
    def usage =
      """
        |Usage: iescargot iltp-problem.p
        |
        | -v              verbose
        | --backend=...   classical first-order prover (escargot,vampire,spass,e)
        | --prooftool     show proof in prooftool
        |""".stripMargin
    val opts = Options().parse( args.toList ) match {
      case Left( err ) =>
        println( s"$err\n$usage" )
        sys.exit( 1 )
      case Right( o ) =>
        o.files match {
          case Seq( _ ) => o
          case Seq() =>
            println( usage )
            sys.exit( 1 )
        }
    }

    LogHandler.verbosity.value = LogHandler.verbosity.value.increase(
      Seq( EscargotLogger ),
      1 + ( if ( opts.verbose ) 2 else 0 ) )

    val tptp = TptpImporter.loadWithIncludes( FilePath( opts.files.head ) )
    val tptpSequent = tptp.toSequent
    implicit val ctx: MutableContext = MutableContext.guess( tptpSequent )
    new IEscargot( opts.backend, opts.method, opts.prooftool, opts.convertLJ, opts.files.head ).
      getLKProof_( tptpSequent ) match {
        case Some( Right( lk ) ) =>
          println( "% SZS status Theorem" )
          print( sequentProofToTptp( lk ) )
        case Some( Left( _ ) ) =>
          println( "% SZS status Non-Theorem" )
        case None =>
          println( "% SZS status Unknown" )
      }
  }
}
