package at.logic.gapt.proofs

import at.logic.gapt.expr._

import scala.collection.GenTraversable

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

  def isAnt: Boolean
  def isSuc: Boolean

  def sameSideAs( that: SequentIndex ): Boolean =
    ( this, that ) match {
      case ( Ant( _ ), Ant( _ ) ) => true
      case ( Suc( _ ), Suc( _ ) ) => true
      case _                      => false
    }
}

case class Ant( k: Int ) extends SequentIndex {
  require( k >= 0, "Indices < 0 are not supported." )

  def +( i: Int ) = Ant( k + i )
  def -( i: Int ) = Ant( k - i )

  override def isAnt: Boolean = true
  override def isSuc: Boolean = false
}

case class Suc( k: Int ) extends SequentIndex {
  require( k >= 0, "Indices < 0 are not supported." )

  def +( i: Int ) = Suc( k + i )
  def -( i: Int ) = Suc( k - i )

  override def isAnt: Boolean = false
  override def isSuc: Boolean = true
}

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

  override def toString: String = s"${antecedent mkString ", "} :- ${succedent mkString ", "}"

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
  def polarizedElements: Seq[( A, Boolean )] = map( _ -> false, _ -> true ).elements

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
   * Concatenate two sequents.  This is equivalent to ++.
   *
   * @param other
   * @return
   */
  @deprecated( "Beware: this is the same as ++.", "2015-10-23" )
  def union[B >: A]( other: Sequent[B] ) = this ++ other

  @deprecated( "Use ++ instead.", "2015-10-23" )
  def compose[B >: A]( other: Sequent[B] ) = this ++ other

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
  @deprecated( "Use +: instead.", "2015-10-23" )
  def addToAntecedent[B >: A]( e: B ): Sequent[B] = e +: this

  /**
   * Adds an element to the antecedent. New elements are always outermost, i.e. on the very left.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the antecedent
   */
  def +:[B >: A]( e: B ) = new Sequent( e +: antecedent, succedent )

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
  @deprecated( "Use :+ instead.", "2015-10-23" )
  def addToSuccedent[B >: A]( e: B ): Sequent[B] = this :+ e

  /**
   * Adds an element to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param e An element of type B > A
   * @return The sequent with e added to the succedent
   */
  def :+[B >: A]( e: B ) = new Sequent( antecedent, succedent :+ e )

  /**
   * Adds a sequence of elements to the succedent. New elements are always outermost, i.e. on the very right.
   *
   * @param es A collection of elements of type B > A.
   * @return The sequent with es added to the succedent.
   */
  def :++[B >: A]( es: GenTraversable[B] ): Sequent[B] = es.foldLeft[Sequent[B]]( this )( _ :+ _ )

  def ++[B >: A]( that: Sequent[B] ) = new Sequent( this.antecedent ++ that.antecedent, this.succedent ++ that.succedent )

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

  def flatMap[B]( f: A => TraversableOnce[B] ): Sequent[B] = flatMap( f, f )

  /**
   * Maps two functions over the antecedent and succedent, respectively.
   *
   * @param f The function to map over the antecedent.
   * @param g The function to map over the succedent.
   * @tparam B The return type of f and g.
   * @return The sequent of type B that results from mapping f and g over the antecedent and succedent, respectively.
   */
  def map[B]( f: ( A ) => B, g: ( A ) => B ) = new Sequent( antecedent map f, succedent map g )

  def flatMap[B]( f: A => TraversableOnce[B], g: A => TraversableOnce[B] ): Sequent[B] =
    Sequent( antecedent flatMap f, succedent flatMap g )

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
  def sortBy[B]( f: A => B )( implicit ord: Ordering[B] ): Sequent[A] = sorted( ord on f )

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
  def indicesSequent: Sequent[SequentIndex] = new Sequent( antecedent.indices map { i => Ant( i ) }, succedent.indices map { i => Suc( i ) } )

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

  def delete( i: SequentIndex ): Sequent[A] = focus( i )._2

  def delete( is: SequentIndex* ): Sequent[A] = ( this /: is.sorted.reverse )( ( acc, i ) => acc delete i )

  def delete( is: Seq[SequentIndex] )( implicit dummyImplicit: DummyImplicit ): Sequent[A] =
    zipWithIndex filterNot { is contains _._2 } map { _._1 }

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

  def indexOfInAnt[B >: A]( elem: B ): SequentIndex = Ant( antecedent indexOf elem )
  def indexOfInSuc[B >: A]( elem: B ): SequentIndex = Suc( succedent indexOf elem )

  def swapped: Sequent[A] = Sequent( succedent, antecedent )

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

  def foreach[U]( f: A => U ): Unit = elements foreach f

  def withFilter( p: A => Boolean ): Sequent[A] = filter( p )
}

object Sequent {
  def apply[A](): Sequent[A] = new Sequent( Seq(), Seq() )

  def apply[A]( ant: Seq[A], succ: Seq[A] ): Sequent[A] = new Sequent( ant, succ )

  def apply[A]( polarizedElements: Seq[( A, Boolean )] ): Sequent[A] =
    Sequent(
      polarizedElements.filter( _._2 == false ).map( _._1 ),
      polarizedElements.filter( _._2 == true ).map( _._1 )
    )

  def unapply[A]( f: Sequent[A] ): Option[( Seq[A], Seq[A] )] = Some( ( f.antecedent, f.succedent ) )
}
