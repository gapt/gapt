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

/**
 * A sequent is a pair of sequences of elements of type A, typically written as a,,1,,,…,a,,m,, :- b,,1,,,…,b,,n,,.
 *
 * @param antecedent The first list.
 * @param succedent The second list.
 * @tparam A The type of the elements of the sequent.
 */
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

  /**
   * Sequence of elements of the sequent.
   *
   * @return Antecedent concatenated with succedent.
   */
  def elements: Seq[A] = antecedent ++ succedent

  /**
   * Sequence of elements together with polarities of type Boolean signifying whether an element is in the antecedent or succedent.
   *
   * FIXME: Make polarities consistent throughout the system (IMO: false = antecedent, true = succedent)
   * @return
   */
  def polarizedElements: Seq[( A, Boolean )] = antecedent.map( _ -> true ) ++ succedent.map( _ -> false )

  /**
   * Returns true iff both cedents are empty.
   *
   * @return
   */
  def isEmpty: Boolean = antecedent.isEmpty && succedent.isEmpty

  def nonEmpty: Boolean = !isEmpty

  /**
   * Takes the multiset difference between two sequents, i.e. each side separately.
   */
  def diff[B >: A]( other: Sequent[B] ) = new Sequent( this.antecedent diff other.antecedent, this.succedent diff other.succedent )

  /**
   * Computes the intersection of two sequents.
   *
   * @param other
   * @return
   */
  def intersect[B >: A]( other: Sequent[B] ) = new Sequent( antecedent intersect other.antecedent, succedent intersect other.succedent )

  /**
   * Computes the union of two sequents.
   *
   * @param other
   * @return
   */
  def union[B >: A]( other: Sequent[B] ) = new Sequent( antecedent union other.antecedent, succedent union other.succedent )

  def compose[B >: A]( other: Sequent[B] ) = new Sequent( antecedent ++ other.antecedent, succedent ++ other.succedent )

  /**
   * Removes duplicate formulas from both cedents.
   *
   * @return
   */
  def distinct = Sequent( antecedent.distinct, succedent.distinct )

  def isSubMultisetOf[B >: A]( other: Sequent[B] ) = ( this diff other ).isEmpty

  /**
   * @param other Another Sequent.
   * @return True iff other contains this pair of sets.
   */
  def isSubsetOf[B >: A]( other: Sequent[B] ) = ( this.distinct diff other.distinct ).isEmpty

  /**
   *
   * @return The sequent in tuple form.
   */
  def toTuple = ( antecedent, succedent )

  /**
   * Adds an element to the antecedent. New elements are always outermost, i.e. on the very left.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the antecedent
   */
  def addToAntecedent[B >: A]( e: B ): Sequent[B] = new Sequent( e +: antecedent, succedent )

  /**
   * Adds an element to the antecedent. New elements are always outermost, i.e. on the very left.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the antecedent
   */
  def +:[B >: A]( e: B ) = addToAntecedent( e )

  /**
   * Adds a sequent of elements to the antecedent. New elements are always outermost, i.e. on the very left.
   *
   * @param es A collection of elements of type B > A.
   * @return The sequent with es added to the antecedent.
   */
  def ++:[B >: A]( es: GenTraversable[B] ): Sequent[B] = ( es :\ this.asInstanceOf[Sequent[B]] )( ( e, acc ) => acc.addToAntecedent( e ) )

  /**
   * Adds an element to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the succedent
   */
  def addToSuccedent[B >: A]( e: B ): Sequent[B] = new Sequent( antecedent, succedent :+ e )

  /**
   * Adds an element to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the succedent
   */
  def :+[B >: A]( e: B ) = addToSuccedent( e )

  /**
   * Adds a sequence of elements to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param es A collection of elements of type B > A.
   * @return The sequent with es added to the succedent.
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

  /**
   * Maps a function over both cedents
   *
   * @param f A function of type A => B
   * @tparam B The return type of f
   * @return The sequent of type B that results from mapping f over both cedents.
   */
  def map[B]( f: ( A ) => B ): Sequent[B] = this map ( f, f )

  /**
   * Maps two functions over the antecedent and succedent, respectively.
   *
   * @param f The function to map over the antecedent.
   * @param g The function to map over the succedent.
   * @tparam B The return type of f and g.
   * @return The sequent of type B that results from mapping f and g over the antecedent and succedent, respectively.
   */
  def map[B]( f: ( A ) => B, g: ( A ) => B ) = new Sequent( antecedent map f, succedent map g )

  /**
   * The sub-sequent of elements satisfying some predicate.
   *
   * @param p A function of type A => Boolean.
   * @return The sequent consisting of only those elements satisfying p.
   */
  def filter( p: A => Boolean ): Sequent[A] = new Sequent( antecedent filter p, succedent filter p )

  /**
   * The sub-sequent of elements not satisfying some predicate.
   *
   * @param p A function of type A => Boolean.
   * @return The sequent consisting of only those elements not satisfying p.
   */
  def filterNot( p: A => Boolean ): Sequent[A] = this filter ( !p( _ ) )

  /**
   * The number of elements in the sequent.
   *
   * @return
   */
  def length = antecedent.length + succedent.length

  /**
   * Synonym for length.
   *
   * @return
   */
  def size = length

  /**
   * A pair consisting of the lengths of the cedents.
   *
   * @return
   */
  def lengths = ( antecedent.length, succedent.length )

  /**
   * Synonym for lengths.
   *
   * @return
   */
  def sizes = lengths

  def sorted[B >: A]( implicit ordering: Ordering[B] ) = new Sequent( antecedent.sorted( ordering ), succedent.sorted( ordering ) )

  /**
   * Returns true iff the sequent contains some element in either cedent.
   *
   * @param el
   * @tparam B
   * @return
   */
  def contains[B]( el: B ): Boolean = elements contains el

  /**
   * Returns the element at some SequentIndex.
   *
   * @param i A SequentIndex, i.e. Ant(k) or Suc(k)
   * @return The k-th element of the antecedent or succedent, depending on the type of i.
   */
  def apply( i: SequentIndex ): A = i match {
    case Ant( k ) => antecedent( k )
    case Suc( k ) => succedent( k )
  }

  /**
   * Returns the range of indices of the sequent.
   *
   * @return
   */
  def indices: Seq[SequentIndex] = ( antecedent.indices map { i => Ant( i ) } ) ++ ( succedent.indices map { i => Suc( i ) } )

  /**
   * Returns the list of indices of elements satisfying some predicate.
   *
   * @param p A function of type A => Boolean.
   * @return
   */
  def indicesWhere( p: A => Boolean ): Seq[SequentIndex] = indices filter { i => p( this( i ) ) }

  /**
   * "Focuses on one element of the seuqent, i.e. returns element at index and the rest of the sequent.
   *
   * @param i A SequentIndex.
   * @return A pair consisting of this(i) and the rest of this.
   */
  def focus( i: SequentIndex ): ( A, Sequent[A] ) = {
    def listFocus( xs: Seq[A] )( i: Int ): ( A, Seq[A] ) = ( xs( i ), xs.take( i ) ++ xs.drop( i + 1 ) )

    i match {
      case Ant( k ) =>
        val ( x, antNew ) = listFocus( antecedent )( k )
        ( x, new Sequent( antNew, succedent ) )
      case Suc( k ) =>
        val ( x, sucNew ) = listFocus( succedent )( k )
        ( x, new Sequent( antecedent, sucNew ) )
    }
  }

  def zipWithIndex: Sequent[( A, SequentIndex )] =
    Sequent(
      antecedent.zipWithIndex.map { case ( a, i ) => a -> Ant( i ) },
      succedent.zipWithIndex.map { case ( b, i ) => b -> Suc( i ) }
    )

  def find( pred: A => Boolean ): Option[SequentIndex] = indicesWhere( pred ).headOption

  def updated[B >: A]( index: SequentIndex, elem: B ): Sequent[B] = index match {
    case Ant( i ) => Sequent( antecedent.updated( i, elem ), succedent )
    case Suc( j ) => Sequent( antecedent, succedent.updated( j, elem ) )
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

