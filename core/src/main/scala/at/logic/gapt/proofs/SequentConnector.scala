package at.logic.gapt.proofs

import at.logic.gapt.proofs.lk.LKProof

import scala.collection.mutable

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 * The most basic use case is that of connecting the conclusion of an LK inference with one of the premises.
 * This is the origin of the names "lowerSizes" and "upperSizes".
 *
 * @param lowerSizes The dimensions of the first ("lower") of the two connected sequents.
 * @param upperSizes The dimensions of the second ("upper") of the two connected sequents.
 * @param parentsSequent A sequent of lists of indices such that for each index i of lowerSequent, parentsSequent(i)
 *                       is the list of indices of the parents of i in upperSequent.
 */
case class SequentConnector( lowerSizes: ( Int, Int ), upperSizes: ( Int, Int ),
                             parentsSequent: Sequent[Seq[SequentIndex]] ) {
  require(
    parentsSequent.sizes == lowerSizes,
    s"Sizes ${parentsSequent.sizes} of parents sequent $parentsSequent don't agree with lower sizes $lowerSizes." )
  require( parentsSequent.elements.flatten.forall { _ withinSizes upperSizes } )

  val ( antL, sucL ) = lowerSizes
  val ( antU, sucU ) = upperSizes
  /**
   * Analogous to parentsSequent, but in the other direction.
   *
   * @return A sequent of lists of indices such that for each index i of upperSequent, childrenSequent(i)
   *                       is the list of indices of the children of i in lowerSequent.
   */
  def childrenSequent: Sequent[Seq[SequentIndex]] = Sequent( antU, sucU ) map children

  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in
   * the upper sequent (if defined).
   *
   * @param idx An index of lowerSequent.
   * @return The list of parents of idx.
   */
  def parents( idx: SequentIndex ): Seq[SequentIndex] = parentsSequent( idx )

  /**
   * Given a SequentIndex for the lower sequent, this returns the parent of that occurrence in the upper sequent
   * (if there is exactly one).
   *
   * @param idx An index of lowerSequent.
   * @return The unique parent of idx.
   */
  def parent( idx: SequentIndex ): SequentIndex = parents( idx ) match {
    case Seq() => throw new NoSuchElementException(
      s"When calling parent on SequentConnector $this: Index $idx has no parent in $parentsSequent." )
    case Seq( p ) => p
    case _ => throw new Exception(
      s"When calling parent on SequentConnector $this: Index $idx has more than one parent in $parentsSequent." )
  }

  /**
   * Given a SequentIndex for the lower sequent, this returns the parent of that occurrence in the upper sequent
   * (if there is exactly one), and None otherwise.
   *
   * @param idx An index of lowerSequent.
   * @return The unique parent of idx.
   */
  def parentOption( idx: SequentIndex ): Option[SequentIndex] = parents( idx ) match {
    case Seq()    => None
    case Seq( p ) => Some( p )
    case _        => None
  }

  /**
   * Given a sequent lowerTs of the same size as the lower sequent, return a sequent of the same size as the upper
   * sequent that contains the parents of the Ts in lowerTs.
   *
   * If we call the returned sequent upperTs, then lowerTs(i) in upperTs(j) for all j in parents(i).
   *
   * The intended use-case is that lowerTs is a sequent of labels for the formulas in the lower sequent.
   * parents(lowerTs) will then contain the correct labels for the formulas in the upper sequent.
   */
  def parents[T]( lowerTs: Sequent[T] ): Sequent[Seq[T]] = {
    require( lowerTs.sizes == lowerSizes )
    childrenSequent map { _ map { lowerTs( _ ) } }
  }

  /**
   * Given a sequent lowerTs of the same size as the lower sequent, return a sequent of the same size as the upper
   * sequent that contains the unique parent of the Ts in lowerTs, or default otherwise.
   */
  def parent[T]( lowerTs: Sequent[T], default: => T = ??? ): Sequent[T] =
    parents( lowerTs ) map {
      case Seq( t ) => t
      case _        => default
    }

  def child[T]( upperTs: Sequent[T], default: => T = ??? ): Sequent[T] =
    inv.parent( upperTs, default )

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in
   * the lower sequent (if defined).
   *
   * @param idx An index of upperSequent.
   * @return The list of children of idx.
   */
  def children( idx: SequentIndex ): Seq[SequentIndex] =
    if ( idx withinSizes upperSizes )
      parentsSequent indicesWhere { _ contains idx }
    else
      throw new IndexOutOfBoundsException

  def children[T]( upperTs: Sequent[T] ): Sequent[Seq[T]] =
    inv.parents( upperTs )

  /**
   * Given a SequentIndex for the upper sequent, this returns the child of that occurrence in the lower sequent
   * (if there is exactly one).
   *
   * @param idx An index of upperSequent.
   * @return The unique child of idx.
   */
  def child( idx: SequentIndex ): SequentIndex = children( idx ) match {
    case Seq() => throw new NoSuchElementException(
      s"When calling child on SequentConnector $this: Index $idx has no child in $parentsSequent." )
    case Seq( c ) => c
    case _ => throw new Exception(
      s"When calling child on SequentConnector $this: Index $idx has more than one child in $parentsSequent." )
  }

  /**
   * Concatenates two SequentConnectors.
   *
   * @param that An SequentConnector. upperSizes of this must be the same as lowerSizes of that.
   * @return An SequentConnector that connects the lower sequent of this with the upper sequent of that.
   */
  def *( that: SequentConnector ) = {
    require( this.upperSizes == that.lowerSizes )
    SequentConnector( this.lowerSizes, that.upperSizes, this.parentsSequent map { _ flatMap that.parents distinct } )
  }

  /**
   * Inverts an SequentConnector.
   *
   * @return This SequentConnector with its lower and upper sizes (and parents and children methods) switched around.
   */
  def inv: SequentConnector = SequentConnector( upperSizes, lowerSizes, childrenSequent )

  /**
   * Forms the union of two SequentConnectors.
   *
   * @param that An SequentConnector. Must have the same upper and lower sizes as this.
   * @return A new SequentConnector o such that for any i, o.parents(i) = this.parents(i) ∪ that.parents(i).
   */
  def +( that: SequentConnector ) = {
    require( this.lowerSizes == that.lowerSizes )
    require( this.upperSizes == that.upperSizes )
    SequentConnector( lowerSizes, upperSizes, Sequent( antL, sucL ).map( i =>
      this.parents( i ) ++ that.parents( i ) distinct ) )
  }

  /**
   * Adds a child/parent pair to an SequentConnector.
   *
   * @param child An index of lowerSequent.
   * @param parent An index of upperSequent.
   * @return A new SequentConnector in which parents(child) contains parent.
   */
  def +( child: SequentIndex, parent: SequentIndex ) = {
    require( child withinSizes lowerSizes )
    require( parent withinSizes upperSizes )
    SequentConnector( lowerSizes, upperSizes,
      parentsSequent.updated( child, parents( child ) :+ parent distinct ) )
  }

  /**
   * Removes a child/parent pair from an SequentConnector.
   * @param child An index of lowerSequent.
   * @param parent An index of upperSequent. Must be a parent of child.
   * @return A new SequentConnector in which parents(child) no longer contains parent.
   */
  def -( child: SequentIndex, parent: SequentIndex ) = {
    require( child withinSizes lowerSizes )
    require( parent withinSizes upperSizes )
    SequentConnector( lowerSizes, upperSizes,
      parentsSequent.updated( child, parents( child ) diff Seq( parent ) ) )
  }
}

object SequentConnector {
  /**
   * Constructs the trivial SequentConnector of a sequent.
   *
   * @param sequent A sequent.
   * @return An SequentConnector that connects every index of sequent to itself.
   */
  def apply( sequent: Sequent[_] ): SequentConnector = SequentConnector( sequent, sequent,
    sequent.indicesSequent map { Seq( _ ) } )

  /**
   * Connects two given sequents via a given parentsSequent.
   */
  def apply( lowerSequent: Sequent[_], upperSequent: Sequent[_],
             parentsSequent: Sequent[Seq[SequentIndex]] ): SequentConnector =
    SequentConnector( lowerSequent.sizes, upperSequent.sizes, parentsSequent )

  /**
   * Creates an SequentConnector that connects all occurrences of an object in the antecedents of
   * two sequents, and analogously
   * for the succedents.
   */
  def findEquals[A]( firstSequent: Sequent[A], secondSequent: Sequent[A] ): SequentConnector = {
    val parentsSequent = firstSequent.map(
      x => secondSequent.indicesWhere( _ == x ) filter { _.isAnt },
      x => secondSequent.indicesWhere( _ == x ) filter { _.isSuc } )

    SequentConnector( firstSequent, secondSequent, parentsSequent )
  }

  /**
   * Guesses a SequentConnector, such that each element in lower gets connected to a different element in upper.
   */
  def guessInjection[A]( fromLower: Sequent[A], toUpper: Sequent[A] ): SequentConnector = {
    val alreadyUsedOldIndices = mutable.Set[SequentIndex]()
    SequentConnector( fromLower, toUpper, fromLower.zipWithIndex.map {
      case ( atom, newIdx ) =>
        val oldIdx = toUpper.indicesWhere( _ == atom ).
          filterNot( alreadyUsedOldIndices.contains ).
          find( newIdx.sameSideAs ).
          getOrElse( throw new IllegalArgumentException(
            s"Cannot find $atom in ${
              toUpper.zipWithIndex
                .filterNot( alreadyUsedOldIndices contains _._2 ).map( _._1 )
            }" ) )
        alreadyUsedOldIndices += oldIdx
        Seq( oldIdx )
    } )
  }
}

object guessPermutation {
  /**
   * Guesses a permutation of formulas in the conclusions of two proofs.
   * @param oldProof The original proof.
   * @param newProof A transformed proof which proves the same end-sequent as `oldProof`.
   * @return A pair consisting of `newProof` and a sequent connector which describes the new
   *         positions of the formulas in `oldProof.conclusion` with respect to `newProof`.
   */
  // FIXME: this is just broken
  def apply( oldProof: LKProof, newProof: LKProof ): ( LKProof, SequentConnector ) =
    ( newProof, SequentConnector.guessInjection( toUpper = newProof.conclusion, fromLower = oldProof.conclusion ).inv )
}
