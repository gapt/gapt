package at.logic.gapt.proofs

/**
 * This class models the connection of formula occurrences between two sequents in a proof.
 *
 */
case class OccConnector[A]( lowerSequent: Sequent[A], upperSequent: Sequent[A], parentsSequent: Sequent[Seq[SequentIndex]] ) {
  require( parentsSequent.sizes == lowerSequent.sizes )
  require( parentsSequent.elements.flatten.toSet subsetOf upperSequent.indices.toSet )

  def childrenSequent = upperSequent.indicesSequent map children

  /**
   * Given a SequentIndex for the lower sequent, this returns the list of parents of that occurrence in the upper sequent (if defined).
   *
   * @param idx
   * @return
   */
  def parents( idx: SequentIndex ): Seq[SequentIndex] = parentsSequent( idx )

  def parents[T]( lowerAs: Sequent[T] ): Sequent[Seq[T]] =
    childrenSequent map { _ map { lowerAs( _ ) } }

  /**
   * Given a SequentIndex for the upper sequent, this returns the list of children of that occurrence in the lower sequent (if defined).
   *
   * @param idx
   * @return
   */
  def children( idx: SequentIndex ): Seq[SequentIndex] =
    if ( upperSequent isDefinedAt idx )
      parentsSequent indicesWhere { _ contains idx }
    else
      throw new IndexOutOfBoundsException

  def *[B >: A]( that: OccConnector[B] ) = {
    require( this.upperSequent == that.lowerSequent )
    OccConnector( this.lowerSequent, that.upperSequent, this.parentsSequent map { _ flatMap that.parents distinct } )
  }

  def inv: OccConnector[A] = OccConnector( upperSequent, lowerSequent, childrenSequent )

  def +[B >: A]( that: OccConnector[B] ) = {
    require( this.lowerSequent == that.lowerSequent )
    require( this.upperSequent == that.upperSequent )
    OccConnector( lowerSequent, upperSequent, lowerSequent.indicesSequent map { i => this.parents( i ) ++ that.parents( i ) } )
  }
}

object OccConnector {
  def apply[A]( sequent: Sequent[A] ): OccConnector[A] = OccConnector( sequent, sequent, sequent.indicesSequent map { Seq( _ ) } )
}
