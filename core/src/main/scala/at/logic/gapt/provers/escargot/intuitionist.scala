package at.logic.gapt.provers.escargot

import ammonite.ops.FilePath
import at.logic.gapt.formats.tptp.TptpParser
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofToLK, deskolemizeET }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.provers.escargot.impl.EscargotLogger
import at.logic.gapt.utils.{ LogHandler, quiet }

object IEscargot {
  def expansionProofToLJ( expProofWithSk: ExpansionProof )( implicit ctx: Context ): Option[LKProof] = {
    val deskExpProof = deskolemizeET( expProofWithSk )
    quiet( ExpansionProofToLK.withIntuitionisticHeuristics( deskExpProof ) ) match {
      case Right( lk ) =>
        val maxSuccSize = lk.subProofs.map( _.endSequent.succedent.toSet.size ).max
        EscargotLogger.warn( s"classical proof has maximum succedent size $maxSuccSize" )
        if ( maxSuccSize <= 1 ) Some( lk ) else None
      case Left( _ ) =>
        EscargotLogger.warn( s"deskolemization failed" )
        None
    }
  }

  def main( args: Array[String] ): Unit = {
    LogHandler.current.value = LogHandler.tstp

    val tptpInputFile = args.toSeq match {
      case Seq() =>
        println( "Usage: iescargot [-v] iltp-problem.p" )
        sys.exit( 1 )
      case Seq( "-v", file ) =>
        LogHandler.verbosity.value = LogHandler.verbosity.value.increase( Seq( EscargotLogger ), 2 )
        file
      case Seq( file ) => file
    }

    val tptp = TptpParser.load( FilePath( tptpInputFile ) )
    val tptpSequent = tptp.toSequent
    implicit val ctx = MutableContext.guess( tptpSequent )
    Escargot.getExpansionProof( tptpSequent ) match {
      case Some( expansion ) =>
        println( "% found classical proof" )
        expansionProofToLJ( expansion ) match {
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
