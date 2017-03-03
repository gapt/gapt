package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ Apps, LambdaExpression, syntacticMatching, _ }
import at.logic.gapt.proofs._

/**
 * The plan is to put all future functions, classes, etc. dealing with Proof schemata into this file.
 * Created by David M. Cerna on 02.02.17.
 */

/**
 * The Point of this class is to allow the instantiation of Proof schemata.
 */
object LKProofSchemata {
  /**
   * Given a proof name found in the context and a set of arguments matching
   * the argument list of the chosen proof name this function constructs an
   * instantiation of that proof. Note that this can result in an infinite
   * loop or no proof depending on how the chosen arguments are used in the
   * the chosen proof
   *
   * @param proofName The name of the linkProof
   * @param args The arguments for the free parameters of the linkProof.
   */
  def Instantiate( proofName: String, args: Seq[LambdaExpression] )( implicit ctx: Context ): LKProof = {

    val ( Some( ( Apps( _, cargs ), _ ) ), Some( invar ) ) = ( ctx.get[Context.ProofNames].names.get( proofName ), ctx.get[Context.ProofDefinitions].components.get( proofName ) )
    require( cargs.size == args.size )
    val Some( ( subs: Substitution, lkp: LKProof ) ) = invar.fold( None )( ( found, search ) => {
      if ( found == None ) {
        val ( Apps( _, vs ), lkp ) = search
        val subs = syntacticMatching( vs.zip( args ) )
        if ( subs.isDefined ) Some( ( subs.getOrElse( Substitution() ), lkp ) )
        else None

      } else found
    } )
    buildProof( subs( lkp ), ( ctx ) )
  }
  /**
   * buildProof uses the  LKVisitor trait to unroll proof links
   *
   */
  object buildProof extends LKVisitor[Context] {
    override def visitProofLink( proof: ProofLink, otherArg: Context ): ( LKProof, SequentConnector ) = {
      val Apps( Const( c, _ ), vs ) = proof.referencedProof
      val upProof = Instantiate( c, vs )( otherArg )
      ( upProof, SequentConnector.guessInjection( upProof.endSequent, proof.conclusion ).inv )
    }
  }

}

class CarriageReturnList {
  private var front: List[Int] = List()
  private var middle: List[Int] = List()
  private var back: List[Int] = List()
  def head: Int = middle.head
  def length: Int = front.length + middle.length + back.length
  def apply( size: Int ) = {
    middle = List( size )
    back = ( size - 1 to 0 ).toList
  }
  def shift(): CarriageReturnList = {
    if ( back.length > 0 ) {
      front :+ middle.head
      middle = List( back.head )
      back = back.tail
    }
    this
  }
  def carriageReturn(): CarriageReturnList = {
    if ( front.length > 0 ) {
      middle = List( front.head )
      back = front.tail ::: back.tail
      front = List()
    } else if ( back.length > 0 ) {
      front = List()
      middle = List( back.head )
      back = back.tail
    } else if ( middle.length > 0 ) {
      front = List()
      middle = List()
      back = List()
    }
    this
  }
}