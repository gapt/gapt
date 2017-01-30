package at.logic.gapt.proofs

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr.{ HOLFormula, Polarity }
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature }

import scala.collection.GenTraversable
import scalaz.{ Functor, Monoid }

/**
 * Represents an index of an element in a sequent.
 *
 * In a sequent, the elements have the following indices:
 * Ant(0), Ant(1), ..., Ant(m) :- Suc(0), Suc(1), ..., Suc(n)
 */
sealed abstract class SequentIndex extends Ordered[SequentIndex] {
  def compare( that: SequentIndex ) = ( this, that ) match {
    case ( Ant( _ ), Suc( _ ) ) => -1
    case ( Suc( _ ), Ant( _ ) ) => 1
    case ( Ant( i ), Ant( j ) ) => i - j
    case ( Suc( i ), Suc( j ) ) => i - j
  }

  /**
   * Increments the index by a natural number.
   *
   * @param i
   */
  def +( i: Int ): SequentIndex

  /**
   * Decrements the index by a natural number.
   *
   * @param i
   */
  def -( i: Int ): SequentIndex

  def polarity: Polarity
  def isAnt = polarity.inAnt
  def isSuc = polarity.inSuc

  def sameSideAs( that: SequentIndex ): Boolean =
    this.polarity == that.polarity

  /** Injective conversion to integers. */
  def toInt: Int

  def withinSizes( p: ( Int, Int ) ): Boolean
}
object SequentIndex {
  def apply( polarity: Polarity, k: Int ): SequentIndex =
    polarity match {
      case Positive => Suc( k )
      case Negative => Ant( k )
    }
}

case class Ant( k: Int ) extends SequentIndex {
  require( k >= 0, "Indices < 0 are not supported." )

  def +( i: Int ) = Ant( k + i )
  def -( i: Int ) = Ant( k - i )

  def polarity = Polarity.InAntecedent

  def toInt = -k - 1

  def withinSizes( p: ( Int, Int ) ): Boolean = k < p._1
}

case class Suc( k: Int ) extends SequentIndex {
  require( k >= 0, "Indices < 0 are not supported." )

  def +( i: Int ) = Suc( k + i )
  def -( i: Int ) = Suc( k - i )

  def polarity = Polarity.InSuccedent

  def toInt = k

  def withinSizes( p: ( Int, Int ) ): Boolean = k < p._2
}

/**
 * A sequent is a pair of sequences of elements of type A, typically written as a,,1,,,…,a,,m,, :- b,,1,,,…,b,,n,,.
 *
 * @param antecedent The first list.
 * @param succedent The second list.
 * @tparam A The type of the elements of the sequent.
 */
case class Sequent[+A]( antecedent: Seq[A], succedent: Seq[A] ) {

  override def toString = toSigRelativeString

  def toSigRelativeString( implicit sig: BabelSignature ): String =
    if ( forall { _.isInstanceOf[HOLFormula] } ) {
      new BabelExporter( unicode = true, sig = sig ).export( this.asInstanceOf[HOLSequent] )
    } else {
      val stringified = this map { _.toString }
      val multiLine = stringified.exists { _ contains "\n" } || stringified.elements.map { _.length + 2 }.sum > 80
      if ( multiLine )
        s"${stringified.antecedent.mkString( ",\n" )}\n:-\n${stringified.succedent.mkString( ",\n" )}"
      else
        s"${stringified.antecedent.mkString( ", " )} :- ${stringified.succedent.mkString( ", " )}"
    }

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
   * @return
   */
  def polarizedElements: Seq[( A, Polarity )] = map( _ -> Polarity.InAntecedent, _ -> Polarity.InSuccedent ).elements

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
  def diff[B >: A]( other: Sequent[B] ) = Sequent( this.antecedent diff other.antecedent, this.succedent diff other.succedent )

  /**
   * Computes the intersection of two sequents.
   *
   * @param other
   * @return
   */
  def intersect[B >: A]( other: Sequent[B] ) = Sequent( antecedent intersect other.antecedent, succedent intersect other.succedent )

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

  def isTaut: Boolean = antecedent intersect succedent nonEmpty

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
  def +:[B >: A]( e: B ) = copy( antecedent = e +: this.antecedent )

  /**
   * Adds a sequent of elements to the antecedent. New elements are always outermost, i.e. on the very left.
   *
   * @param es A collection of elements of type B > A.
   * @return The sequent with es added to the antecedent.
   */
  def ++:[B >: A]( es: GenTraversable[B] ): Sequent[B] = es.foldRight[Sequent[B]]( this )( _ +: _ )

  /**
   * Adds an element to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the succedent
   */
  def :+[B >: A]( e: B ) = copy( succedent = this.succedent :+ e )

  /**
   * Adds a sequence of elements to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param es A collection of elements of type B > A.
   * @return The sequent with es added to the succedent.
   */
  def :++[B >: A]( es: GenTraversable[B] ): Sequent[B] = es.foldLeft[Sequent[B]]( this )( _ :+ _ )

  def ++[B >: A]( that: Sequent[B] ) = Sequent( this.antecedent ++ that.antecedent, this.succedent ++ that.succedent )

  def removeFromAntecedent[B]( e: B ) = Sequent( antecedent filterNot ( _ == e ), succedent )

  def removeFromSuccedent[B]( e: B ) = Sequent( antecedent, succedent filterNot ( _ == e ) )

  /**
   * Maps a function over both cedents
   *
   * @param f A function of type A => B
   * @tparam B The return type of f
   * @return The sequent of type B that results from mapping f over both cedents.
   */
  def map[B]( f: ( A ) => B ): Sequent[B] = this map ( f, f )

  def flatMap[B]( f: A => TraversableOnce[B] ): Sequent[B] = flatMap( f, f )

  def collect[B]( f: PartialFunction[A, B] ): Sequent[B] =
    Sequent( antecedent collect f, succedent collect f )

  /**
   * Maps two functions over the antecedent and succedent, respectively.
   *
   * @param f The function to map over the antecedent.
   * @param g The function to map over the succedent.
   * @tparam B The return type of f and g.
   * @return The sequent of type B that results from mapping f and g over the antecedent and succedent, respectively.
   */
  def map[B]( f: ( A ) => B, g: ( A ) => B ) = Sequent( antecedent map f, succedent map g )

  def flatMap[B]( f: A => TraversableOnce[B], g: A => TraversableOnce[B] ): Sequent[B] =
    Sequent( antecedent flatMap f, succedent flatMap g )

  /**
   * The sub-sequent of elements satisfying some predicate.
   *
   * @param p A function of type A => Boolean.
   * @return The sequent consisting of only those elements satisfying p.
   */
  def filter( p: A => Boolean ): Sequent[A] = Sequent( antecedent filter p, succedent filter p )

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

  def sorted[B >: A]( implicit ordering: Ordering[B] ) = Sequent( antecedent.sorted( ordering ), succedent.sorted( ordering ) )
  def sortBy[B]( f: A => B )( implicit ord: Ordering[B] ): Sequent[A] = sorted( ord on f )

  /**
   * Returns true iff the sequent contains some element in either cedent.
   *
   * @param el
   * @tparam B
   * @return
   */
  def contains[B]( el: B ): Boolean = elements contains el

  def cedent( polarity: Polarity ) = polarity match {
    case Positive => succedent
    case Negative => antecedent
  }

  def contains[B]( el: B, polarity: Polarity ): Boolean =
    cedent( polarity ).contains( el )

  /**
   * Returns the element at some SequentIndex.
   *
   * @param i A SequentIndex, i.e. Ant(k) or Suc(k)
   * @return The k-th element of the antecedent or succedent, depending on the type of i.
   */
  def apply( i: SequentIndex ): A = {
    try {
      i match {
        case Ant( k ) => antecedent( k )
        case Suc( k ) => succedent( k )
      }
    } catch {
      case _: IndexOutOfBoundsException => throw new IndexOutOfBoundsException( s"Sequent $this not defined at index $i." )
    }
  }

  def apply( is: Seq[SequentIndex] ): Seq[A] = is map this.apply

  /**
   * Tests whether the sequent is defined at the supplied SequentIndex.
   *
   * @param i
   * @return
   */
  def isDefinedAt( i: SequentIndex ): Boolean = i match {
    case Ant( k ) => antecedent.isDefinedAt( k )
    case Suc( k ) => succedent.isDefinedAt( k )
  }

  /**
   * Returns the range of indices of the sequent as a sequence.
   *
   * @return
   */
  def indices: Seq[SequentIndex] = indicesSequent.elements

  /**
   * Returns the range of indices of the sequent as a sequent.
   *
   * @return
   */
  def indicesSequent: Sequent[SequentIndex] = Sequent( sizes._1, sizes._2 )

  /**
   * Returns the list of indices of elements satisfying some predicate.
   *
   * @param p A function of type A => Boolean.
   * @return
   */
  def indicesWhere( p: A => Boolean ): Seq[SequentIndex] = indices filter { i => p( this( i ) ) }

  def indicesWherePol( p: A => Boolean, pol: Polarity ): Seq[SequentIndex] =
    indices filter { i => ( i.polarity == pol ) && p( this( i ) ) }

  /**
   * Focuses on one element of the sequent, i.e. returns element at index and the rest of the sequent.
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

  def delete( i: SequentIndex ): Sequent[A] = delete( Seq( i ) )

  def delete( is: Seq[SequentIndex] ): Sequent[A] =
    zipWithIndex filterNot { is contains _._2 } map { _._1 }

  def delete( is: SequentIndex* )( implicit d: DummyImplicit ): Sequent[A] = delete( is )

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

  def indexOfOption[B >: A]( elem: B ): Option[SequentIndex] = find( _ == elem )
  def indexOf[B >: A]( elem: B ): SequentIndex = indexOfOption( elem ) get

  def indexOfPol[B >: A]( elem: B, polarity: Polarity ): SequentIndex =
    SequentIndex( polarity, cedent( polarity ).indexOf( elem ) )
  def indexOfInAnt[B >: A]( elem: B ): SequentIndex = indexOfPol( elem, Polarity.InAntecedent )
  def indexOfInSuc[B >: A]( elem: B ): SequentIndex = indexOfPol( elem, Polarity.InSuccedent )

  def indexOfPolOption[B >: A]( elem: B, pol: Polarity ): Option[SequentIndex] =
    cedent( pol ).indexOf( elem ) match {
      case -1  => None
      case idx => Some( SequentIndex( pol, idx ) )
    }

  def swapped: Sequent[A] = Sequent( succedent, antecedent )

  def exists( p: A => Boolean ): Boolean = antecedent.exists( p ) || succedent.exists( p )
  def forall( p: A => Boolean ): Boolean = antecedent.forall( p ) && succedent.forall( p )

  def zip[B]( that: Sequent[B] ): Sequent[( A, B )] =
    Sequent( this.antecedent zip that.antecedent, this.succedent zip that.succedent )

  def replaceAt[B >: A]( i: SequentIndex, el: B ) = delete( i ).insertAt( i, el )

  def insertAt[B >: A]( i: SequentIndex, el: B ) = i match {
    case Ant( j ) =>
      Sequent( antecedent.take( j ) ++ Seq( el ) ++ antecedent.drop( j ), succedent )

    case Suc( j ) =>
      Sequent( antecedent, succedent.take( j ) ++ Seq( el ) ++ succedent.drop( j ) )
  }

  def foreach[U]( f: A => U ): Unit = {
    antecedent foreach f
    succedent foreach f
  }

  def withFilter( p: A => Boolean ): Sequent[A] = filter( p )

  def groupBy[B]( f: A => B ): Sequent[( B, Seq[A] )] =
    Sequent( antecedent groupBy f toSeq, succedent groupBy f toSeq )
}

object Sequent {
  def apply[A](): Sequent[A] = Sequent( Seq(), Seq() )

  def apply[A]( polarizedElements: Seq[( A, Polarity )] ): Sequent[A] = {
    val ( ant, suc ) = polarizedElements.view.partition( _._2.inAnt )
    Sequent( ant.map( _._1 ), suc.map( _._1 ) )
  }

  /**
   * Returns a generic sequent of sizes (m, n): Ant(0),…,Ant(m-1) :- Suc(0),…,Suc(n-1)
   */
  def apply( m: Int, n: Int ): Sequent[SequentIndex] = ( 0 until m ).map { Ant } ++: Sequent() :++ ( 0 until n ).map { Suc }

  implicit val SequentFunctor = new Functor[Sequent] {
    def map[A, B]( fa: Sequent[A] )( f: A => B ): Sequent[B] = fa.map( f )
  }

  implicit def SequentMonoid[A] = new Monoid[Sequent[A]] {
    override def zero = Sequent()
    override def append( s1: Sequent[A], s2: => Sequent[A] ): Sequent[A] = s1 ++ s2
  }
}
