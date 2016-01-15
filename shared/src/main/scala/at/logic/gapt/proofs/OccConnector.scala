package at.logic.gapt.proofs

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 * The most basic use case is that of connecting the conclusion of an LK inference with one of the premises.
 * This is the origin of the names "lowerSequent" and "upperSequent".
 *
 * @param lowerSequent One of the two sequents to be connected.
 * @param upperSequent The other of the two sequents to be connected.
 * @param parentsSequent A sequent of lists of indices such that for each index i of lowerSequent, parentsSequent(i)
 *                       is the list of indices of the parents of i in upperSequent.
 * @tparam A The type of sequents that this connects.
 */
case class OccConnector[+A]( lowerSequent: Sequent[A], upperSequent: Sequent[A], parentsSequent: Sequent[Seq[SequentIndex]] ) {
  require( parentsSequent.sizes == lowerSequent.sizes )
  require( parentsSequent.elements.flatten.toSet subsetOf upperSequent.indices.toSet )

  /**
   * Analogous to parentsSequent, but in the other direction.
   *
   * @return A sequent of lists of indices such that for each index i of upperSequent, childrenSequent(i)
   *                       is the list of indices of the children of i in lowerSequent.
   */
  def childrenSequent = upperSequent.indicesSequent map children

  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in the upper sequent (if defined).
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
    case Seq()    => throw new NoSuchElementException( s"Index $idx has no parent in sequent $upperSequent." )
    case Seq( p ) => p
    case _        => throw new Exception( s"Index $idx has more than one parent in sequent $upperSequent." )
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
    require( lowerTs.sizes == lowerSequent.sizes )
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

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in the lower sequent (if defined).
   *
   * @param idx An index of upperSequent.
   * @return The list of children of idx.
   */
  def children( idx: SequentIndex ): Seq[SequentIndex] =
    if ( upperSequent isDefinedAt idx )
      parentsSequent indicesWhere { _ contains idx }
    else
      throw new IndexOutOfBoundsException

  /**
   * Given a SequentIndex for the upper sequent, this returns the child of that occurrence in the lower sequent
   * (if there is exactly one).
   *
   * @param idx An index of upperSequent.
   * @return The unique child of idx.
   */
  def child( idx: SequentIndex ): SequentIndex = children( idx ) match {
    case Seq()    => throw new NoSuchElementException( s"Index $idx has no child in sequent $lowerSequent." )
    case Seq( c ) => c
    case _        => throw new Exception( s"Index $idx has more than one child in sequent $lowerSequent." )
  }

  /**
   * Concatenates two OccConnectors.
   *
   * @param that An OccConnector. upperSequent of this must have the same dimensions as lowerSequent of that.
   * @tparam B The type of that.
   * @return An OccConnector that connects the lower sequent of this with the upper sequent of that.
   */
  def *[B >: A]( that: OccConnector[B] ) = {
    require( this.upperSequent.sizes == that.lowerSequent.sizes )
    OccConnector( this.lowerSequent, that.upperSequent, this.parentsSequent map { _ flatMap that.parents distinct } )
  }

  /**
   * Inverts an OccConnector.
   *
   * @return This OccConnector with its lower and upper sequents (and parents and children methods) switched around.
   */
  def inv: OccConnector[A] = OccConnector( upperSequent, lowerSequent, childrenSequent )

  /**
   * Forms the union of two OccConnectors.
   *
   * @param that An OccConnector. Must have the same upper and lower sequent as this.
   * @tparam B The type of B.
   * @return A new OccConnector o such that for any i, o.parents(i) = this.parents(i) ∪ that.parents(i).
   */
  def +[B >: A]( that: OccConnector[B] ) = {
    require( this.lowerSequent == that.lowerSequent )
    require( this.upperSequent == that.upperSequent )
    OccConnector( lowerSequent, upperSequent, lowerSequent.indicesSequent map { i => this.parents( i ) ++ that.parents( i ) distinct } )
  }

  /**
   * Adds a child/parent pair to an OccConnector.
   *
   * @param child An index of lowerSequent.
   * @param parent An index of upperSequent.
   * @return A new OccConnector in which parents(child) contains parent.
   */
  def +( child: SequentIndex, parent: SequentIndex ) = {
    require( lowerSequent isDefinedAt child )
    require( upperSequent isDefinedAt parent )
    OccConnector( lowerSequent, upperSequent,
      parentsSequent.updated( child, parents( child ) :+ parent distinct ) )
  }
}

object OccConnector {
  /**
   * Constructs the trivial OccConnector of a sequent.
   *
   * @param sequent A sequent.
   * @tparam A The type of sequent.
   * @return An OccConnector that connects every index of sequent to itself.
   */
  def apply[A]( sequent: Sequent[A] ): OccConnector[A] = OccConnector( sequent, sequent, sequent.indicesSequent map { Seq( _ ) } )
}
