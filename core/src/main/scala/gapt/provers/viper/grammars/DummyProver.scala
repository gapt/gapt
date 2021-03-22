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
import gapt.formats._
import gapt.formats.leancop._
import gapt.provers.groundFreeVariables

case class DummyProver( insts: Map[Formula, Option[ExpansionProof]] ) {

  def erasureReduction = new OneShotProver {
    import gapt.proofs.reduction._
    override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      val ( seqground, subst ) = groundFreeVariables( seq )
      val reduction = ErasureReductionET
      val ( folProblem, back ) = reduction forward seqground
      folProblem match {
        case Sequent( _, Seq( f ) ) => {
          print( "checking for proof: " + f + "\n" + insts.keySet.toString() + "\n" )
          insts.get( f ) match {
            case Some( Some( t ) ) => Some( TermReplacement.undoGrounding( back( t ), subst ) )
            case _                 => None
          }
        }
        case _ => None
      }
    }
    override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = None

  }
  def predicateReduction = new OneShotProver {
    import gapt.proofs.reduction._
    override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      val ( seqground, subst ) = groundFreeVariables( seq )
      val reduction = PredicateReductionET |> ErasureReductionET
      val ( folProblem, back ) = reduction forward seqground
      folProblem match {
        case Sequent( _, Seq( f ) ) => {
          print( "checking for proof: " + f + "\n" + insts.keySet.toString() + "\n" )
          insts.get( f ) match {
            case Some( Some( t ) ) => Some( TermReplacement.undoGrounding( back( t ), subst ) )
            case _                 => None
          }
        }
        case _ => None
      }
    }
    override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = None

  }
}
object DummyProverHelper {
  def getListOfExpPrf( dir: String ): List[ExpansionProof] = {
    val d = new File( dir )
    if ( d.exists && d.isDirectory ) {
      val paths = d.listFiles.toList.map( t => InputFile.fromJavaFile( t ) )
      val expSeq = paths.map( t => {
        print( "Parsing: " + t.toString() + "\n" )
        LeanCoPParser.getExpansionProof( t )
      } ).flatten
      val expPrf = expSeq.map( t => ExpansionProof( t ) )
      if ( expSeq.size != paths.size ) List[ExpansionProof]()
      else expPrf
    } else List[ExpansionProof]()
  }
  def MakeProofDict( dir: String ): Map[Formula, Option[ExpansionProof]] = {
    val ExpPrf = getListOfExpPrf( dir )
    val lPairs = ExpPrf.map( t => ( t.shallow.succedent.toList( 0 ) -> Some( t ) ) )
    if ( lPairs.size != ExpPrf.size ) Map[Formula, Option[ExpansionProof]]()
    else lPairs.toMap
  }
  def enoughSolutions( dir: String, n: Int ): List[String] = {
    val d = new File( dir )
    if ( d.exists && d.isDirectory ) {
      val dict = d.listFiles.toList.filter( _.isDirectory )
      if ( dict.isEmpty && d.listFiles.length == n ) return ( d.getAbsolutePath() +: List.empty[String] )
      else if ( dict.isEmpty ) return List.empty[String]
      else return dict.map( x => enoughSolutions( x.getAbsolutePath(), n ) ).flatten
    } else return List.empty[String]
  }
}
