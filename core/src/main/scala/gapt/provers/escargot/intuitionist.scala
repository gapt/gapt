package gapt.provers.escargot

import ammonite.ops.FilePath
import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.formats.tptp.TptpParser
import gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, ExpansionProofToMG3i, ExpansionProofToMG3iViaSAT, deskolemizeET, formulaToExpansionTree }
import gapt.proofs.lk.{ LKProof, isMaeharaMG3i }
import gapt.proofs.{ Context, MutableContext }
import gapt.prooftool.LKProofViewer
import gapt.provers.Prover
import gapt.provers.eprover.EProver
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.sat.Sat4j
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire
import gapt.utils.{ LogHandler, quiet }

object IEscargot {
  def expansionProofToMG3i(
    expProofWithSk:  ExpansionProof,
    filename:        String,
    mg3isat:         Boolean,
    mg4ip:           Boolean,
    showInProoftool: Boolean )( implicit ctx: Context ): Option[LKProof] = {
    val deskExpProof = deskolemizeET( expProofWithSk )
    EscargotLogger.warn( "deskolemization finished" )
    quiet {
      if ( mg3isat ) ExpansionProofToMG3iViaSAT( deskExpProof )
      else if ( mg4ip ) ExpansionProofToMG3i( deskExpProof )
      else ExpansionProofToLK.withIntuitionisticHeuristics( deskExpProof )
    } match {
      case Right( lk ) =>
        if ( showInProoftool ) {
          val viewer = new LKProofViewer( filename, lk )
          viewer.markNonIntuitionisticInferences()
          viewer.showFrame()
        }
        val maxSuccSize = lk.subProofs.map( _.endSequent.succedent.toSet.size ).max
        EscargotLogger.warn( s"classical proof has maximum succedent size $maxSuccSize" )
        val inMG3i = isMaeharaMG3i( lk )
        EscargotLogger.warn( s"classical proof is in mG3i: $inMG3i" )
        if ( inMG3i ) Some( lk ) else None
      case Left( ( _, unprovable ) ) =>
        EscargotLogger.warn( s"stuck at: $unprovable" )
        None
    }
  }

  case class Options(
      verbose:   Boolean     = false,
      backend:   Prover      = Escargot,
      prooftool: Boolean     = false,
      mg3isat:   Boolean     = false,
      mg4ip:     Boolean     = false,
      files:     Seq[String] = Seq() ) {
    def parse( args: List[String] ): Either[String, Options] =
      args match {
        case "--backend=vampire" :: rest       => copy( backend = Vampire ).parse( rest )
        case "--backend=spass" :: rest         => copy( backend = SPASS ).parse( rest )
        case "--backend=escargot" :: rest      => copy( backend = Escargot ).parse( rest )
        case "--backend=e" :: rest             => copy( backend = new EProver( extraArgs = Seq( "--auto" ) ) ).parse( rest )
        case "--prooftool" :: rest             => copy( prooftool = true ).parse( rest )
        case "--mg4ip" :: rest                 => copy( mg4ip = true ).parse( rest )
        case "--mg3isat" :: rest               => copy( mg3isat = true ).parse( rest )
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
        filter( QfUfEscargot.isValid ).
        map( formulaToExpansionTree( _ ) ).
        map( ExpansionProof ) ) match {
      case Some( expansion ) =>
        println( "% found classical proof" )
        expansionProofToMG3i( expansion, filename = opts.files.head, mg4ip = opts.mg4ip,
          mg3isat = opts.mg3isat, showInProoftool = opts.prooftool ) match {
          case Some( lj ) =>
            require( lj.endSequent.isSubsetOf( tptpSequent ) )
            println( "% SZS status Theorem" )
            lj.toString.lines.map( "% " + _ ).foreach( println )
          case None =>
            println( "% SZS status Unknown" )
            println( "% constructivization failed" )
        }
      case None =>
        println( "% SZS status Non-Theorem" )
    }
  }
}
