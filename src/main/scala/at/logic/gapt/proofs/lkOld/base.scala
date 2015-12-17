package at.logic.gapt.proofs.lkOld.base

import at.logic.gapt.expr.hol.{ HOLPosition, HOLOrdering }
import at.logic.gapt.proofs.{ HOLSequent, Suc, Ant, SequentIndex }
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.utils.ds.trees._

object HOLSequentOrdering extends HOLSequentOrdering

/**
 * Ordering for sequents.
 */
class HOLSequentOrdering extends Ordering[HOLSequent] {
  def compare( x: HOLSequent, y: HOLSequent ): Int = {
    if ( x.antecedent.size < y.antecedent.size ) -1 else if ( y.antecedent.size < x.antecedent.size ) 1 else if ( x.antecedent.size == y.antecedent.size && x.succedent.size < y.succedent.size ) -1 else if ( x.antecedent.size == y.antecedent.size && y.succedent.size < x.succedent.size ) 1 else {
      assert( x.antecedent.size == y.antecedent.size &&
        x.succedent.size == y.succedent.size, "Implementation error comparing HOLSequents!" )
      val xs = x.sorted( HOLOrdering ).elements
      val ys = y.sorted( HOLOrdering ).elements
      val xys = xs zip ys
      xys.foldLeft( 0 )( ( rv, pair ) => {
        //as long as it is undecided, we compare pairs
        if ( rv == 0 ) HOLOrdering.compare( pair._1, pair._2 )
        //otherwise we pass the result on
        else rv
      } )
    }
  }
}

// exceptions
class LKRuleException( msg: String ) extends RuleException( msg )
class LKRuleCreationException( msg: String ) extends LKRuleException( msg )
//these two classes allow detailed error diagnosis
case class LKUnaryRuleCreationException( name: String, parent: LKProof, aux: List[HOLFormula] )
    extends LKRuleCreationException( "" ) {
  override def getMessage = "Could not create lk rule " + name + " from parent " + parent.root + " with auxiliary formulas " + aux.mkString( ", " )
}
case class LKBinaryRuleCreationException( name: String, parent1: LKProof, aux1: HOLFormula, parent2: LKProof, aux2: HOLFormula )
    extends LKRuleCreationException( "" ) {
  override def getMessage = "Could not create lk rule " + name + " from left parent " + parent1.root + " with auxiliary formula " + aux1 +
    " and right parent " + parent2.root + " with auxiliary formula " + aux2
}

class FormulaNotExistsException( msg: String ) extends LKRuleException( msg )

trait LKProof extends TreeProof[OccSequent] with Tree[OccSequent] {
  def getDescendantInLowerSequent( fo: FormulaOccurrence ): Option[FormulaOccurrence] = {
    ( root.antecedent ++ root.succedent ).filter( ( occ: FormulaOccurrence ) => occ.isDescendantOf( fo, reflexive = true ) ) match {
      case x :: Nil => Some( x )
      case Nil      => None
      case _        => throw new LKRuleException( "Illegal lower sequent in rule in application of getDescendantInLowerSequent: More than one such formula exists" )
    }
  }

  def containsDescendantOf( fo: FormulaOccurrence ): Boolean = getDescendantInLowerSequent( fo ) match {
    case Some( _ ) => true
    case None      => false
  }

  override def toString = rule + "(" + root.toHOLSequent.toString + ")"
}
trait NullaryLKProof extends LeafTree[OccSequent] with LKProof with NullaryTreeProof[OccSequent] {
  override def toString = rule + "(" + root.toHOLSequent.toString + ")"
}
trait UnaryLKProof extends UnaryTree[OccSequent] with LKProof with UnaryTreeProof[OccSequent] {
  override def uProof = t.asInstanceOf[LKProof]
  override def toString = rule + "(" + root.toHOLSequent.toString + ")"
}
trait BinaryLKProof extends BinaryTree[OccSequent] with LKProof with BinaryTreeProof[OccSequent] {
  override def uProof1 = t1.asInstanceOf[LKProof]
  override def uProof2 = t2.asInstanceOf[LKProof]
  override def toString = rule + "(" + root.toHOLSequent.toString + ")"
}

// traits denoting having auxiliary and main formulas
trait AuxiliaryFormulas {
  // for each upper sequent we have a list of occurrences
  def aux: List[List[FormulaOccurrence]]
}
trait PrincipalFormulas {
  def prin: List[FormulaOccurrence]
}
trait SubstitutionTerm {
  def subst: LambdaExpression
}
trait Eigenvariable {
  def eigenvar: Var
}

trait TermPositions {
  def termPos: Seq[HOLPosition]
}

// method for creating the context of the lower sequent. Essentially creating nre occurrences
// create new formula occurrences in the new context
object createContext {
  def apply( set: Seq[FormulaOccurrence] ): Seq[FormulaOccurrence] =
    set.map( x =>
      x.factory.createFormulaOccurrence( x.formula.asInstanceOf[HOLFormula], x :: Nil ) )
}

