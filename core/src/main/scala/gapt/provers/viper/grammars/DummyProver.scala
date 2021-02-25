package gapt.provers.viper.grammars

import gapt.expr._
import gapt.proofs.lk.LKProof
import gapt.expr.formula.Formula
import gapt.proofs.expansion._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.{ HOLSequent, Sequent, Suc }
import gapt.provers.OneShotProver
import gapt.utils.Maybe
import gapt.proofs.reduction._
import java.io.File
import gapt.formats.ClasspathInputFile
import gapt.formats.leancop._

case class DummyProver( insts: Map[Formula, Option[ExpansionProof]] ) extends OneShotProver {
  override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    val reduction = ErasureReductionET
    val ( folProblem, back ) = reduction forward seq
    folProblem match {
      case Sequent( _, Seq( f ) ) => {
        insts.get( f ) match {
          case Some( Some( t ) ) => Some( back( t ) )
          case _                 => None
        }
      }
      case _ => None
    }
  }
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = None
}
object DummyProverHelper {
  def getListOfExpPrf( dir: String ): List[ExpansionProof] = {
    val d = new File( dir )
    if ( d.exists && d.isDirectory ) {
      val ClassPaths = d.listFiles.toList.map( t => ClasspathInputFile( t.toString ) )
      val expSeq = ClassPaths.map( t => LeanCoPParser.getExpansionProof( t ) ).flatten
      val expPrf = expSeq.map( t => ExpansionProof( t ) )
      if ( expSeq.size != ClassPaths.size ) List[ExpansionProof]()
      expPrf
    } else List[ExpansionProof]()
  }
  getListOfExpPrf( "PLCOP/prop_9_proofs" )
  def MakeProofDict( dir: String ): Map[Formula, Option[ExpansionProof]] = {
    val ExpPrf = getListOfExpPrf( dir )
    val lPairs = ExpPrf.map( t => ExpansionProofToLK( t ) match {
      case Left( r )  => None
      case Right( r ) => Some( ( r.conclusion.succedent.toList( 0 ) -> Some( t ) ) )
    } ).flatten
    if ( lPairs.size != ExpPrf.size ) Map[Formula, Option[ExpansionProof]]()
    else lPairs.toMap
  }
}
