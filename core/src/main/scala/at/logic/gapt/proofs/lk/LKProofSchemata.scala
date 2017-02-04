package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ LambdaExpression, _ }
import at.logic.gapt.proofs._
import scala.math._

/**
 * The plan is to put all future function, classes, etc. dealing with proof schemata into this file.
 * Created by Ermine516 on 02.02.17.
 */

/**
 * The Point of this class is to allow the instantiation of proof schemata.
 * We provide two functions, one for Proof schemata indexed by inductive datatypes
 * and one for proof schemata indexed by numeric expressions only.
 */
class LKProofSchemata {

  /**
   * Note that there is no guarantee that instantiated proof schemata will result in a finite
   * proof, thus one must provide a maxdepth function which takes a sequence of lambda expressions
   * and returns an integer. That is the max depth to unroll the proof schemata two.
   * @param ProofName The name of the proof
   * @param args The arguements for the free parameters of the proof.
   * @param MaxDepth The function computing the maximum depth.
   */
  def InstantiateNumerically( ProofName: String, args: Seq[LambdaExpression],
                              MaxDepth: ( Seq[LambdaExpression] => Int ) = MaxDepthInit )( implicit ctx: Context ): Option[LKProof] = {
    //We should require the first numericArgs args to be variable free.
    //if numericArgs is greater than the size of args we have an error
    //if the size of args is greater than the expected number of arges for proofName
    //we have an error

    /*We could assume that the deepest the recursion can go is the maximum term depth of the
      parameter arguements multiplied together. This is a sensible assumption
      Thus, if we exceed this value the s
     */

    None
  }
  /**
   * This is the initial max depth function and just computes the depth of the the indivitual
   * arguments and multiplies them together.
   * @param args The arguements for the free parameters of the proof.
   */
  def MaxDepthInit( args: Seq[LambdaExpression] ): Int =
    args.fold( 1 )( ( tot, curLe ) => {
      val one: Int = termDepth( curLe.asInstanceOf[LambdaExpression] ) match {
        case Some( i ) => i
        case None      => -1
      }
      if ( one >= 0 ) tot.asInstanceOf[Int] * one
      else -1
    } ).asInstanceOf[Int]
  /**
   * A helper function for MaxDepthInit
   * @param Term The term to compute the depth of
   */
  def termDepth( Term: LambdaExpression ): Option[Int] = {
    Term match {
      case at.logic.gapt.expr.Const( _, _ ) => Some( 1 )
      case Var( _, _ )                      => Some( 1 )
      case Apps( func, args ) =>
        val two: Int = args.map( term => termDepth( term ) ).fold( 0 )( ( x, y ) => y match {
          case Some( i ) => if ( 0 <= x.asInstanceOf[Int] ) max( x.asInstanceOf[Int], i.asInstanceOf[Int] ) else -1
          case None      => -1
        } ).asInstanceOf[Int]
        val three: Int = termDepth( func ) match {
          case Some( i ) => i
          case None      => -1
        }
        Some( if ( three < 0 ) -1 else three + two )

      case Abs( _, t ) => Some( termDepth( t ) match {
        case Some( i ) => if ( i != -1 ) max( 1, i ) else -1
        case None      => -1
      } )
      case _ => None
    }
  }

  def InstantiateByInductiveType( ProofName: String, args: Seq[LambdaPosition], numericArgs: Int )( implicit ctx: Context ): Option[LKProof] = {
    //We should require the first numericArgs args to be variable free.
    //if numericArgs is greater than the size of args we have an error
    //if the size of args is greater than the expected number of arges for proofName
    //we have an error
    None
  }
}
