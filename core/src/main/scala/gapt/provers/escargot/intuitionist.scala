package gapt.provers.escargot

import ammonite.ops.FilePath
import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.formats.tptp.{ TptpParser, sequentProofToTptp }
import gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, ExpansionProofToMG3i, ExpansionProofToMG3iViaSAT, deskolemizeET, formulaToExpansionTree }
import gapt.proofs.lk.{ LKProof, isMaeharaMG3i }
import gapt.proofs.{ Context, HOLSequent, MutableContext }
import gapt.prooftool.LKProofViewer
import gapt.provers.{ OneShotProver, Prover }
import gapt.provers.congruence.SimpleSmtSolver
import gapt.provers.eprover.EProver
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire
import gapt.utils.{ LogHandler, Maybe, quiet }

class IEscargot(
    backend:         Prover        = Escargot,
    method:          ExpToLKMethod = ExpToLKMethod.MG3iViaSAT,
    showInProoftool: Boolean       = false,
    filename:        String        = "" ) extends OneShotProver {
  def expansionProofToMG3i( expProofWithSk: ExpansionProof )( implicit ctx: Context ): Option[LKProof] = {
    val deskExpProof = deskolemizeET( expProofWithSk )
    EscargotLogger.warn( "converting expansion proof to LK" )
    quiet( method.convert( deskExpProof ) ) match {
      case Right( lk ) =>
        EscargotLogger.warn( s"LK proof has ${lk.dagLike.size} inferences" )
        val maxSuccSize = lk.subProofs.map( _.endSequent.succedent.toSet.size ).max
        EscargotLogger.warn( s"LK proof has maximum succedent size $maxSuccSize" )
        val inMG3i = isMaeharaMG3i( lk )
        EscargotLogger.warn( s"LK proof is in mG3i: $inMG3i" )
        if ( showInProoftool ) {
          val viewer = new LKProofViewer( filename, lk )
          viewer.markNonIntuitionisticInferences()
          viewer.showFrame()
        }
        if ( inMG3i ) Some( lk ) else None
      case Left( unprovable ) =>
        EscargotLogger.warn( s"stuck at: $unprovable" )
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

    if ( !containsQuantifierOnLogicalLevel( seq.toImplication ) ) {
      if ( !SimpleSmtSolver.isValid( seq ) ) Some( Left( () ) )
      else expansionProofToMG3i( ExpansionProof( formulaToExpansionTree( seq ) ) ) match {
        case Some( lk ) => Some( Right( lk ) )
        case None       => if ( method.isComplete ) Some( Left( () ) ) else None
      }
    } else {
      backend.getExpansionProof( seq ) match {
        case Some( expansion ) =>
          EscargotLogger.warn( "found classical expansion proof" )
          expansionProofToMG3i( expansion ) match {
            case Some( lk ) =>
              require( lk.endSequent.isSubsetOf( seq ) )
              Some( Right( lk ) )
            case None =>
              EscargotLogger.warn( "constructivization failed" )
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
  showInProoftool = false,
  filename = "" ) {
  import ExpToLKMethod._

  case class Options(
      verbose:   Boolean       = false,
      backend:   Prover        = Escargot,
      prooftool: Boolean       = false,
      method:    ExpToLKMethod = MG3iViaSAT,
      files:     Seq[String]   = Seq() ) {
    def parse( args: List[String] ): Either[String, Options] =
      args match {
        case "--backend=vampire" :: rest       => copy( backend = Vampire ).parse( rest )
        case "--backend=spass" :: rest         => copy( backend = SPASS ).parse( rest )
        case "--backend=escargot" :: rest      => copy( backend = Escargot ).parse( rest )
        case "--backend=e" :: rest             => copy( backend = new EProver( extraArgs = Seq( "--auto" ) ) ).parse( rest )
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

    if ( opts.verbose )
      LogHandler.verbosity.value = LogHandler.verbosity.value.increase( Seq( EscargotLogger ), 2 )

    val tptp = TptpParser.load( FilePath( opts.files.head ) )
    val tptpSequent = tptp.toSequent
    implicit val ctx: MutableContext = MutableContext.guess( tptpSequent )
    new IEscargot( opts.backend, opts.method, opts.prooftool, opts.files.head ).
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
