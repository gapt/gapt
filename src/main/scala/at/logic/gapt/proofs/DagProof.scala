package at.logic.gapt.proofs

import scala.collection.mutable
import scala.runtime.ScalaRunTime

trait DagProof[A <: DagProof[A]] extends Product { self: A =>
  /**
   * The immediate subproofs of this rule.
   */
  def immediateSubProofs: Seq[A]

  /**
   * The name of the rule (in symbols).
   */
  def name: String = longName

  /**
   * The name of the rule (in words).
   */
  def longName: String = productPrefix

  /**
   * Iterate over all sub-proofs including this in post-order.
   */
  def foreach( f: A => Unit ): Unit = {
    immediateSubProofs foreach { _ foreach f }
    f( self )
  }

  /**
   * Iterate over all sub-proofs including this in post-order, ignoring duplicates.
   * @return Set of all visited sub-proofs including this.
   */
  def dagLikeForeach( f: A => Unit ): Set[A] = {
    val seen = mutable.Set[A]()

    def traverse( p: A ): Unit =
      if ( !( seen contains p ) ) {
        p.immediateSubProofs foreach traverse
        seen += p
        f( p )
      }

    traverse( self )
    seen.toSet
  }

  /**
   * Iterate over all sub-proofs including this breadth-first, ignoring duplicates.
   * @return Set of all visited sub-proofs including this.
   */
  def dagLikeBreadthFirstForeach( f: A => Unit ): Set[A] = {
    val seen = mutable.Set[A]()
    val queue = mutable.Queue[A]( self )

    while ( queue.nonEmpty ) {
      val next = queue.dequeue()
      if ( !( seen contains next ) ) {
        seen += next
        f( next )
        queue ++= next.immediateSubProofs
      }
    }

    seen.toSet
  }

  /**
   * A sequence of all sub-proofs including this in post-order.
   */
  def postOrder: Seq[A] = {
    val subProofs = Seq.newBuilder[A]
    foreach { subProofs += _ }
    subProofs.result()
  }

  /**
   * A sequence of all sub-proofs including this in post-order, ignoring duplicates.
   */
  def dagLikePostOrder: Seq[A] = {
    val subProofs = Seq.newBuilder[A]
    dagLikeForeach { subProofs += _ }
    subProofs.result()
  }

  /**
   * A sequence of all sub-proofs including this in post-order, ignoring duplicates.
   */
  def dagLikeBreadthFirst: Seq[A] = {
    val subProofs = Seq.newBuilder[A]
    dagLikeBreadthFirstForeach { subProofs += _ }
    subProofs.result()
  }

  /**
   *  Set of all sub-proofs including this.
   */
  def subProofs: Set[A] = dagLikeForeach { _ => () }

  protected def stepString( subProofLabels: Map[Any, String] ) =
    s"$longName(${productIterator.map { param => subProofLabels.getOrElse( param, param.toString ) }.mkString( ", " )})"

  override def toString: String = {
    val steps = dagLikeBreadthFirst.reverse.zipWithIndex map { case ( p, i ) => ( p, s"p${i + 1}" ) }
    val subProofLabels: Map[Any, String] = steps.toMap

    val output = new StringBuilder()
    steps.reverse foreach {
      case ( step, number ) =>
        output ++= s"[$number] ${step.stepString( subProofLabels )}\n"
    }
    output.result()
  }

  override val hashCode = ScalaRunTime._hashCode( this )

}
