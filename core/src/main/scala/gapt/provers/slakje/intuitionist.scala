package gapt.provers.slakje

import ammonite.ops.FilePath
import gapt.expr._
import gapt.expr.fol.folSubTerms
import gapt.expr.hol.{ atoms, containsQuantifierOnLogicalLevel, isEssentiallyCNF }
import gapt.formats.tptp.{ TptpImporter, sequentProofToTptp }
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion._
import gapt.proofs.lk.{ LKProof, MG3iToLJ, isMaeharaMG3i, normalizeLKt }
import gapt.prooftool.LKProofViewer
import gapt.provers.congruence.SimpleSmtSolver
import gapt.provers.eprover.EProver
import gapt.provers.escargot.Escargot
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.spass.SPASS
import gapt.provers.vampire.{ Vampire, VampireCASC }
import gapt.provers.{ OneShotProver, Prover }
import gapt.utils.{ LogHandler, Logger, Maybe, quiet }

object SlakjeLogger extends Logger( "slakje" ); import SlakjeLogger._

object heuristicDecidabilityInstantiation {
  def apply( proof: ExpansionProof ): ExpansionProof = {
    val terms = folSubTerms( proof.deep.toImplication ).groupBy( _.ty )
    val cands = proof.shallow.antecedent.filter( isCandidate )
    metric( "heuristic_inst_num_formulas", cands.size )
    ExpansionProof( ETMerge(
      ( for ( cand <- cands ) yield formulaToExpansionTree(
        cand,
        mkSubsts( boundVariables( cand ), terms ), Polarity.InAntecedent ) ) ++:
        proof.expansionSequent ) )
  }

  def mkSubsts( vars: Set[Var], terms: Map[Ty, Set[Expr]] ): Set[Substitution] = {
    import cats.instances.list._
    import cats.syntax.traverse._
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

class Slakje(
    backend:         Prover        = Escargot,
    method:          ExpToLKMethod = ExpToLKMethod.MG3iViaSAT,
    showInProoftool: Boolean       = false,
    convertToLJ:     Boolean       = false,
    filename:        String        = "" ) extends OneShotProver {
  def expansionProofToMG3i( expProofWithSk: ExpansionProof )( implicit ctx: Context ): Option[LKProof] = {
    // TODO: mine proofs for congruences
    val hasEquality = atoms( expProofWithSk.shallow ).exists { case Eq( _, _ ) => true case _ => false }
    metric( "has_equality", hasEquality )
    val deskExpProof = time( "deskolemization" ) { deskolemizeET( expProofWithSk, removeCongruences = hasEquality ) }
    info( "converting expansion proof to LK" )
    time( "exptolk" ) { quiet( method.convert( deskExpProof ) ) } match {
      case Right( lk0 ) =>
        val lk = if ( !convertToLJ ) lk0 else time( "convert_lj" ) { normalizeLKt.lk( MG3iToLJ( lk0 ) ) }
        metric( "lk_dag_size", lk.dagLike.size )
        info( s"LK proof has ${lk.dagLike.size} inferences" )
        val maxSuccSize = lk.subProofs.map( _.endSequent.succedent.toSet.size ).max
        metric( "lk_max_succ_size", maxSuccSize )
        info( s"LK proof has maximum succedent size $maxSuccSize" )
        val inMG3i = isMaeharaMG3i( lk )
        metric( "lk_mg3i", inMG3i )
        info( s"LK proof is in mG3i: $inMG3i" )
        if ( showInProoftool ) {
          val viewer = new LKProofViewer( filename, lk )
          viewer.markNonIntuitionisticInferences()
          viewer.showFrame()
        }
        if ( inMG3i ) Some( lk ) else None
      case Left( unprovable ) =>
        info( s"stuck at: $unprovable" )
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
    metric( "ess_cnf", essentiallyCNF )
    if ( essentiallyCNF )
      info( "problem is essentially in clause normal form" )

    val quantifierFree = !containsQuantifierOnLogicalLevel( seq.toImplication )
    metric( "quant_free", quantifierFree )
    if ( quantifierFree ) {
      val qfUfValid = time( "prover" ) { SimpleSmtSolver.isValid( seq ) }
      metric( "prover_valid", qfUfValid )
      if ( !qfUfValid ) Some( Left( () ) ) else {
        if ( essentiallyCNF ) {
          info( "SZS status Theorem" )
          metric( "status", "theorem" )
        }
        val maybeLK = expansionProofToMG3i( ExpansionProof( formulaToExpansionTree( seq ) ) )
        metric( "constructivization_ok", maybeLK.isDefined )
        maybeLK match {
          case Some( lk ) => Some( Right( lk ) )
          case None       => if ( method.isComplete ) Some( Left( () ) ) else None
        }
      }
    } else {
      time( "prover" ) { quiet( backend.getExpansionProof( seq ) ) } match {
        case Some( expansion0 ) =>
          metric( "prover_valid", true )
          info( "found classical expansion proof" )
          metric( "exp_size", numberOfInstancesET( expansion0 ) )
          val proofEssentiallyCNF = essentiallyCNF || isEssentiallyCNF( expansion0.shallow )
          metric( "proof_ess_cnf", proofEssentiallyCNF )
          if ( !essentiallyCNF && proofEssentiallyCNF )
            info( "axioms used by proof are essentially in clause normal form" )
          if ( proofEssentiallyCNF ) {
            metric( "status", "theorem" )
            info( "SZS status Theorem" )
          }
          val expansion1 = ETWeakening( expansion0, seq )
          val expansion2 = pushWeakeningsUp( expansion1 )
          val expansion3 = time( "heuristic_inst" ) { heuristicDecidabilityInstantiation( expansion2 ) }
          val maybeLK = expansionProofToMG3i( expansion3 )
          metric( "constructivization_ok", maybeLK.isDefined )
          maybeLK match {
            case Some( lk ) =>
              require( lk.endSequent.isSubsetOf( seq ) )
              Some( Right( lk ) )
            case None =>
              info( "constructivization failed" )
              None
          }
        case None =>
          // TODO: make sure that Vampire/SPASS/E only return None for satisfiable problems
          metric( "prover_valid", false )
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

object Slakje extends Slakje(
  backend = Escargot,
  method = ExpToLKMethod.MG3iViaSAT,
  convertToLJ = true,
  showInProoftool = false,
  filename = "" ) {
  import ExpToLKMethod._

  private case class Options(
      verbose:    Boolean        = false,
      backend:    Prover         = Escargot,
      prooftool:  Boolean        = false,
      convertLJ:  Boolean        = false,
      method:     ExpToLKMethod  = MG3iViaSAT,
      metrics:    Boolean        = false,
      printProof: Boolean        = true,
      file:       Option[String] = None )

  private val optionParser = new scopt.OptionParser[Options]( "slakje" ) {
    val backends = Map(
      "vampire" -> Vampire,
      "vampirecasc" -> VampireCASC,
      "spass" -> SPASS,
      "e" -> new EProver( extraArgs = Seq( "--auto" ) ),
      "escargot" -> Escargot )
    opt[String]( "backend" ).
      valueName( s"(${backends.keys.mkString( "|" )})" ).
      text( "first-order prover to use as backend (default is escargot)" ).
      action( ( b, c ) => c.copy( backend = backends( b ) ) )

    val methods = Map(
      "heuristic" -> Heuristic,
      "mg4ip" -> MG4ip,
      "mg3isat" -> MG3iViaSAT )
    opt[String]( "method" ).
      valueName( s"(${methods.keys.mkString( "|" )})" ).
      text( "method to convert expansion proofs to LK (default is mg3isat)" ).
      action( ( m, c ) => c.copy( method = methods( m ) ) )

    opt[Boolean]( "print-proof" ).
      action( ( x, c ) => c.copy( printProof = x ) ).
      valueName( "(true|false)" ).
      text( "print the LK proof as a TPTP derivation" )

    opt[Unit]( 'v', "verbose" ).
      action( ( _, c ) => c.copy( verbose = true ) ).
      text( "produce more output" )

    opt[Unit]( "metrics" ).
      action( ( _, c ) => c.copy( metrics = true ) ).
      text( "display measurements for experiments" )

    opt[Unit]( "prooftool" ).
      action( ( _, c ) => c.copy( prooftool = true ) ).
      text( "show proof in prooftool" )

    opt[Unit]( "lj" ).
      action( ( _, c ) => c.copy( convertLJ = true ) ).
      text( "convert proof to cut-free lj" )

    arg[String]( "iltp-problem.p" ).
      text( "input file in TPTP format" ).
      action( ( x, c ) => c.copy( file = Some( x ) ) )
  }

  def main( args: Array[String] ): Unit = try {
    val opts = optionParser.parse( args, Options() ).getOrElse {
      System.exit( 1 )
      throw new IllegalStateException
    }

    LogHandler.current.value =
      if ( opts.metrics ) new LogHandler.tstpWithMetrics else LogHandler.tstp
    LogHandler.verbosity.value = LogHandler.verbosity.value.increase(
      Seq( SlakjeLogger, EscargotLogger ),
      1 + ( if ( opts.verbose ) 2 else 0 ) )

    val file = opts.file.get

    metric( "file", file )
    metric( "backend", opts.backend.getClass.getSimpleName.replace( "$", "" ) )
    metric( "method", opts.method )

    time( "total" ) {
      val tptp = time( "parse" ) { TptpImporter.loadWithIncludes( FilePath( file ) ) }
      val tptpSequent = tptp.toSequent
      implicit val ctx: MutableContext = MutableContext.guess( tptpSequent )
      new Slakje( opts.backend, opts.method, opts.prooftool, opts.convertLJ, file ).
        getLKProof_( tptpSequent ) match {
          case Some( Right( lk ) ) =>
            metric( "status", "theorem" )
            println( "% SZS status Theorem" )
            if ( opts.printProof )
              time( "print_proof" ) { print( sequentProofToTptp( lk ) ) }
          case Some( Left( _ ) ) =>
            metric( "status", "nontheorem" )
            println( "% SZS status Non-Theorem" )
          case None =>
            metric( "status", "unknown" )
            println( "% SZS status Unknown" )
        }
    }
  } catch {
    case t: Throwable =>
      metric( "exception", t.toString.take( 200 ) )
      throw t
  }
}
