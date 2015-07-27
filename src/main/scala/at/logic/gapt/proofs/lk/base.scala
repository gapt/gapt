package at.logic.gapt.proofs.lk.base

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr.hol.{ HOLPosition, HOLOrdering }
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.utils.ds.trees._

import scala.collection.GenTraversable

sealed abstract class SequentIndex

case class Ant( k: Int ) extends SequentIndex

case class Suc( k: Int ) extends SequentIndex

class Sequent[+A]( val antecedent: Seq[A], val succedent: Seq[A] ) {
  /**
   * Equality treating each side of the sequent as list, i.e. respecting order and multiplicity.
   */
  override def equals( other: Any ): Boolean = other match {
    case seq: Sequent[Any] => ( antecedent equals seq.antecedent ) && ( succedent equals seq.succedent )
    case _                 => false
  }

  override def hashCode: Int = 31 * antecedent.hashCode() + succedent.hashCode()

  override def toString: String =
    this.antecedent.mkString( "," ) + " :- " + this.succedent.mkString( "," )

  /**
   * Equality treating each side of the sequent as a set.
   */
  def setEquals[B]( other: Sequent[B] ): Boolean = ( other isSubsetOf this ) && ( this isSubsetOf other )

  /**
   * Equality treating each side of the sequent as a multiset.
   */
  def multiSetEquals[B]( other: Sequent[B] ): Boolean = ( other isSubMultisetOf this ) && ( this isSubMultisetOf other )

  def elements: Seq[A] = antecedent ++ succedent

  def polarizedElements: Seq[( A, Boolean )] = antecedent.map( _ -> true ) ++ succedent.map( _ -> false )

  def isEmpty: Boolean = antecedent.isEmpty && succedent.isEmpty

  def nonEmpty: Boolean = !isEmpty

  /**
   * Takes the multiset difference between two sequents, i.e. each side separately.
   */
  def diff[B >: A]( other: Sequent[B] ) = Sequent( this.antecedent diff other.antecedent, this.succedent diff other.succedent )

  /**
   * Computes the intersection of two sequents.
   *
   * @param other
   * @return
   */
  def intersect[B >: A]( other: Sequent[B] ) = Sequent( antecedent intersect other.antecedent, succedent intersect other.succedent )

  /**
   * Computes the union of two sequents.
   *
   * @param other
   * @return
   */
  def union[B >: A]( other: Sequent[B] ) = Sequent( antecedent union other.antecedent, succedent union other.succedent )

  def compose[B >: A]( other: Sequent[B] ) = Sequent( antecedent ++ other.antecedent, succedent ++ other.succedent )

  /**
   * Removes duplicate formulas from both cedents.
   *
   * @return
   */
  def distinct = Sequent( antecedent.distinct, succedent.distinct )

  def isSubMultisetOf[B >: A]( other: Sequent[B] ) = ( this diff other ).isEmpty

  /**
   * @param other Another HOLSequent.
   * @return True iff other contains this pair of sets.
   */
  def isSubsetOf[B >: A]( other: Sequent[B] ) = ( this.distinct diff other.distinct ).isEmpty

  /**
   *
   * @return The sequent in tuple form.
   */
  def toTuple = ( antecedent, succedent )

  /**
   *
   * @param e An element of type A
   * @return The sequent with e added to the antecedent
   */
  def addToAntecedent[B >: A]( e: B ): Sequent[B] = new Sequent( e +: antecedent, succedent )

  /**
   *
   * @param e An element
   * @return The sequent with e added to the antecedent
   */
  def +:[B >: A]( e: B ) = addToAntecedent( e )

  /**
   *
   * @param fs A collection of HOLFormulas.
   * @return The sequent with fs added to the antecedent.
   */
  def ++:[B >: A]( es: GenTraversable[B] ): Sequent[B] = ( es :\ this.asInstanceOf[Sequent[B]] )( ( e, acc ) => acc.addToAntecedent( e ) )

  /**
   *
   * @param e An element of type A
   * @return The sequent with e added to the antecedent
   */
  def addToSuccedent[B >: A]( e: B ): Sequent[B] = new Sequent( antecedent, succedent :+ e )

  /**
   *
   * @param f A HOLFormula
   * @return The sequent with f added to the succedent
   */
  def :+[B >: A]( e: B ) = addToSuccedent( e )

  /**
   *
   * @param fs A collection of HOLFormulas.
   * @return The sequent with fs added to the succedent.
   */
  def :++[B >: A]( es: GenTraversable[B] ): Sequent[B] = ( this.asInstanceOf[Sequent[B]] /: es )( ( acc, e ) => acc.addToSuccedent( e ) )

  def ++[B >: A]( that: Sequent[B] ) = this union that

  def removeFromAntecedent[B]( e: B ) = new Sequent( antecedent filterNot ( _ == e ), succedent )

  def removeFromSuccedent[B]( e: B ) = new Sequent( antecedent, succedent filterNot ( _ == e ) )

  def replaceInAntecedent[B, C]( from: B, to: C ) = {
    require( antecedent.contains( from ) )
    new Sequent( antecedent.map( e => if ( e == from ) to else e ), succedent )
  }

  def replaceInSuccedent[B, C]( from: B, to: C ) = {
    require( succedent.contains( from ) )
    new Sequent( antecedent, succedent.map( e => if ( e == from ) to else e ) )
  }

  def map[B]( f: ( A ) => B ): Sequent[B] = this map ( f, f )

  def map[B]( f: ( A ) => B, g: ( A ) => B ) = new Sequent( antecedent map f, succedent map g )

  def filter( p: A => Boolean ): Sequent[A] = new Sequent( antecedent filter p, succedent filter p )

  def filterNot( p: A => Boolean ): Sequent[A] = this filter ( !p( _ ) )

  def length = antecedent.length + succedent.length

  def size = length

  def sorted[B >: A]( implicit ordering: Ordering[B] ) = new Sequent( antecedent.sorted( ordering ), succedent.sorted( ordering ) )

  def contains[B]( el: B ): Boolean = elements contains el

  def apply( i: SequentIndex ): A = i match {
    case Ant( k ) => antecedent( k )
    case Suc( k ) => succedent( k )
  }
}

object Sequent {
  def apply[A](): Sequent[A] = new Sequent( Seq(), Seq() )

  def apply[A]( ant: Seq[A], succ: Seq[A] ): Sequent[A] = new Sequent( ant, succ )

  def apply[A]( polarizedElements: Seq[( A, Boolean )] ): Sequent[A] =
    Sequent(
      polarizedElements.filter( _._2 == true ).map( _._1 ),
      polarizedElements.filter( _._2 == false ).map( _._1 )
    )

  def unapply[A]( f: Sequent[A] ): Option[( Seq[A], Seq[A] )] = Some( ( f.antecedent, f.succedent ) )
}

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
  def termPos: List[HOLPosition]
}

// method for creating the context of the lower sequent. Essentially creating nre occurrences
// create new formula occurrences in the new context
object createContext {
  def apply( set: Seq[FormulaOccurrence] ): Seq[FormulaOccurrence] =
    set.map( x =>
      x.factory.createFormulaOccurrence( x.formula.asInstanceOf[HOLFormula], x :: Nil ) )
}

