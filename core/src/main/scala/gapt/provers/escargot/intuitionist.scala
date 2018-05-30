package gapt.provers.escargot

import ammonite.ops.FilePath
import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.formats.tptp.{ TptpParser, sequentProofToTptp }
import gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, ExpansionProofToMG3i, ExpansionProofToMG3iViaSAT, deskolemizeET, formulaToExpansionTree }
import gapt.proofs.lk.{ LKProof, isMaeharaMG3i }
import gapt.proofs.{ Context, HOLSequent, MutableContext }
import gapt.prooftool.LKProofViewer
import gapt.provers.Prover
import gapt.provers.congruence.SimpleSmtSolver
import gapt.provers.eprover.EProver
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire
import gapt.utils.{ LogHandler, quiet }

object IEscargot {
  def expansionProofToMG3i(
    expProofWithSk:  ExpansionProof,
    filename:        String,
    method:          ExpToLKMethod,
    showInProoftool: Boolean )( implicit ctx: Context ): Option[LKProof] = {
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

  sealed trait ExpToLKMethod {
    def convert( exp: ExpansionProof )( implicit ctx: Context ): Either[HOLSequent, LKProof]
  }
  case object MG3iViaSAT extends ExpToLKMethod {
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
    implicit val ctx = MutableContext.guess( tptpSequent )
    ( if ( containsQuantifierOnLogicalLevel( tptpSequent.toImplication ) )
      opts.backend.getExpansionProof( tptpSequent )
    else
      Some( tptpSequent ).
        filter( SimpleSmtSolver.isValid ).
        map( formulaToExpansionTree( _ ) ).
        map( ExpansionProof ) ) match {
      case Some( expansion ) =>
        println( "% found classical expansion proof" )
        expansionProofToMG3i( expansion, filename = opts.files.head,
          method = opts.method, showInProoftool = opts.prooftool ) match {
          case Some( lk ) =>
            require( lk.endSequent.isSubsetOf( tptpSequent ) )
            println( "% SZS status Theorem" )
            print( sequentProofToTptp( lk ) )
          case None =>
            println( "% SZS status Unknown" )
            println( "% constructivization failed" )
        }
      case None =>
        println( "% SZS status Non-Theorem" )
    }
  }
}
