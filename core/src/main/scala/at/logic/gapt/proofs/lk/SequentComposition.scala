package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.Expr
import at.logic.gapt.proofs.{ HOLSequent, Sequent }

//This trait is used to tag constructs which should be allowed within
//a sequent compositions.
//currently We allow CLSTerm and Sequent[A]
trait SequentTerm

//A generalization of Sequents allowing variables
//and predicates at the sequent level.

case class SequentComposition( composedSequents: Set[SequentTerm] ) {
  //This function returns the composition of all
  //sequent terms in the given SequentComposition which
  //have the same type as the base of the composition
  def towards[A]( base: Sequent[A] = Sequent[A]() ): Sequent[A] =
    composedSequents.foldLeft( base )( ( x, y ) =>
      y match {
        case Sequent( _, _ ) => x ++ y.asInstanceOf[Sequent[A]]
        case _               => x
      } )
  //This function returns a new SequentComposition which
  //only contains the CLSTerms of the original SequentComposition
  def towardsCLSTerms(): SequentComposition =
    SequentComposition( composedSequents.foldLeft( Set[SequentTerm]() )( ( x, y ) =>
      y match {
        case CLSTerm( _, _, _ ) => x + y
        case _                  => x
      } ) )
  //This function returns a new SequentComposition which contains
  //all sequentterms in the composition which are not of the given
  // type represented by the base of the composition
  def awayFrom[A]( base: Sequent[A] = Sequent[A]() ): SequentComposition =
    SequentComposition( composedSequents.foldLeft( Set[SequentTerm]() )( ( x, y ) =>
      y match {
        case Sequent( _, _ ) => x
        case _               => x + y
      } ) )
  //Checks if the SequentComposition only contains
  //sequent terms of a given sequent type
  def isUniformTorwards[A]( base: Sequent[A] = Sequent[A]() ): Boolean =
    composedSequents.forall( x => x.isInstanceOf[Sequent[A]] )

  //Checks if the SequentComposition contains sequentterms
  //other than those of the given base type

  def isCompositeawayFrom[A]( base: Sequent[A] = Sequent[A]() ): Boolean =
    !composedSequents.forall( x => x.isInstanceOf[Sequent[A]] )

  //Checks if the SequentComposition contains no sequentterms
  //of the given base type
  def isUniformawayFrom[A]( base: Sequent[A] = Sequent[A]() ): Boolean =
    composedSequents.forall( x => !x.isInstanceOf[Sequent[A]] )

  def +( e: SequentTerm ): SequentComposition = SequentComposition( composedSequents + e )
  def ++( e: SequentComposition ): SequentComposition = SequentComposition( composedSequents ++ e.composedSequents )

}

//A object containing special apply method for sequent compositions.
object SequentComposition {
  def apply(): SequentComposition = SequentComposition( Set[SequentTerm]() )
  def apply( aTerm: SequentTerm ): SequentComposition = SequentComposition( Set( aTerm ) )
}

//A special type of sequent composition for schematic clause set extraction
case class CLSTerm( proofName: String, CutConfig: HOLSequent, args: Seq[Expr] ) extends SequentTerm {}