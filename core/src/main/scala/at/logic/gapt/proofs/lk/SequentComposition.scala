package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.Expr
import at.logic.gapt.proofs.{HOLSequent, Sequent}

//A generalization of Sequents allowing variables
//not predicates at the sequent level.

trait SequentTerm
case class SequentComposition( composedSequents: Set[SequentTerm]){
  //This function returns the composition of all
  //sequent terms in the given SequentComposition which
  //have the same type as the base of the composition
  def towards[A](base:Sequent[A]= Sequent[A]()):Sequent[A] =
    composedSequents.foldLeft(base)((x,y)=>
      y match {
        case Sequent(_, _) => x ++ y.asInstanceOf[Sequent[A]]
        case _ => x
      })
  //This function returns a new SequentComposition which
  //only contains the CLSTerms of the original SequentComposition
  def towardsCLSTerms():SequentComposition =
    SequentComposition(composedSequents.foldLeft(Set[SequentTerm]())((x,y)=>
      y match {
        case CLSTerm(_, _,_) => x + y
        case _ => x
      }))
  //This function returns a new SequentComposition which contains
  //all sequentterms in the composition which are not of the given
  // type represented by the base of the composition
  def awayFrom[A](base:Sequent[A] =Sequent[A]() ):SequentComposition =
    SequentComposition(composedSequents.foldLeft(Set[SequentTerm]())((x,y)=>
      y match {
        case Sequent(_, _) => x
        case _ => x + y
      }))
  //Checks if the SequentComposition only contains
  //sequent terms of a given sequent type
  def isUniformTorwards[A](base:Sequent[A]=Sequent[A]() ):Boolean =
    composedSequents.forall(x => x.isInstanceOf[Sequent[A]])

  //Checks if the SequentComposition contains sequentterms
  //other than those of the given base type
  def isCompositeawayFrom[A](base:Sequent[A]=Sequent[A]() ):Boolean =
    !composedSequents.forall(x => x.isInstanceOf[Sequent[A]])

  //Checks if the SequentComposition contains no sequentterms
  //of the given base type
  def isUniformawayFrom[A](base:Sequent[A]=Sequent[A]() ):Boolean =
    composedSequents.forall(x => !x.isInstanceOf[Sequent[A]])

  def +( e: SequentTerm ): SequentComposition = SequentComposition(composedSequents + e)
  def ++( e: SequentComposition ): SequentComposition = SequentComposition(composedSequents ++ e.composedSequents)

}

object SequentComposition {
  def apply(): SequentComposition = SequentComposition(Set[SequentTerm]())
  def apply(aTerm:SequentTerm): SequentComposition = SequentComposition(Set(aTerm))
}


case class CLSTerm(proofName:String,CutConfig:HOLSequent, args:Seq[Expr]) extends SequentTerm {}