package at.logic.gapt.proofs

import scala.collection.mutable
import scala.runtime.ScalaRunTime

/**
 * DAG-like proof.
 *
 * Proofs are recursive structures that are represented as case classes.  Equality is standard case class equality
 * (but implemented in such a way that it is efficient on DAGs).
 *
 * @tparam Proof  The type of proof, e.g. [[at.logic.gapt.proofs.lkNew.LKProof]].
 */
trait DagProof[Proof <: DagProof[Proof]] extends Product { self: Proof =>
  /**
   * The immediate subproofs of this rule.
   */
  def immediateSubProofs: Seq[Proof]

  /**
   * The name of this rule (in symbols).
   */
  def name: String = longName

  /**
   * The name of this rule (in words).
   */
  def longName: String = productPrefix

  /** Operations that view the sub-proofs as a tree. */
  object treeLike {

    /**
     * Iterate over all sub-proofs including this in post-order.
     */
    def foreach( f: Proof => Unit ): Unit = {
      for ( p <- immediateSubProofs ) p.treeLike foreach f
      f( self )
    }

    /**
     * A sequence of all sub-proofs including this in post-order.
     */
    def postOrder: Seq[Proof] = {
      val subProofs = Seq.newBuilder[Proof]
      for ( p <- treeLike ) subProofs += p
      subProofs.result()
    }

    /**
     * Number of sub-proofs including this, counting duplicates.
     */
    def size: BigInt = {
      val memo = mutable.Map[Proof, BigInt]()
      def f( subProof: Proof ): BigInt =
        memo.getOrElseUpdate(
          subProof,
          subProof.immediateSubProofs.map( f ).sum + 1
        )
      f( self )
    }
  }

  /** Operations that view the sub-proofs as a DAG, which ignore duplicate sub-proofs. */
  object dagLike {

    /**
     * Iterate over all sub-proofs including this in post-order, ignoring duplicates.
     * @return Set of all visited sub-proofs including this.
     */
    def foreach( f: Proof => Unit ): Set[Proof] = {
      val seen = mutable.Set[Proof]()

      def traverse( p: Proof ): Unit =
        if ( !( seen contains p ) ) {
          p.immediateSubProofs foreach traverse
          seen += p
          f( p )
        }

      traverse( self )
      seen.toSet
    }

    /**
     * A sequence of all sub-proofs including this in post-order, ignoring duplicates.
     */
    def postOrder: Seq[Proof] = {
      val subProofs = Seq.newBuilder[Proof]
      for ( p <- dagLike ) subProofs += p
      subProofs.result()
    }

    /**
     * A sequence of all sub-proofs including this in post-order, ignoring duplicates.
     */
    def breadthFirst: Seq[Proof] = {
      val seen = mutable.Set[Proof]()
      val result = Seq.newBuilder[Proof]
      val queue = mutable.Queue[Proof]( self )

      while ( queue.nonEmpty ) {
        val next = queue.dequeue()
        if ( !( seen contains next ) ) {
          seen += next
          result += next
          queue ++= next.immediateSubProofs
        }
      }

      result.result()
    }

    /**
     * Number of sub-proofs including this, not counting duplicates.
     */
    def size: Int = subProofs.size
  }

  /**
   * Set of all (transitive) sub-proofs including this.
   */
  def subProofs: Set[Proof] = dagLike foreach { _ => () }

  /**
   * Depth of the proof, which is the maximum length of a path you can take via [[immediateSubProofs]].
   */
  def depth: Int = {
    val memo = mutable.Map[Proof, Int]()
    def f( subProof: Proof ): Int = memo.getOrElseUpdate(
      subProof,
      ( subProof.immediateSubProofs.map( f ) :+ 0 ).max + 1
    )
    f( this )
  }

  protected def stepString( subProofLabels: Map[Any, String] ) =
    s"$longName(${productIterator.map { param => subProofLabels.getOrElse( param, param.toString ) }.mkString( ", " )})"

  override def toString: String = {
    val steps = dagLike.postOrder.zipWithIndex map { case ( p, i ) => ( p, s"p${i + 1}" ) }
    val subProofLabels: Map[Any, String] = steps.toMap

    val output = new StringBuilder()
    steps.reverse foreach {
      case ( step, number ) =>
        output ++= s"[$number] ${step.stepString( subProofLabels )}\n"
    }
    output.result()
  }

  override val hashCode = ScalaRunTime._hashCode( this )

  override def equals( that: Any ) = {
    case class PtrPair( a: AnyRef, b: AnyRef ) {
      override def hashCode = 31 * System.identityHashCode( a ) + System.identityHashCode( b )
      override def equals( that: Any ) = that match {
        case PtrPair( a_, b_ ) => ( a eq a_ ) && ( b eq b_ )
        case _                 => false
      }
    }

    val areEqual = mutable.Set[PtrPair]()
    def checkEqual( a: DagProof[_], b: DagProof[_] ): Boolean =
      if ( a eq b ) true
      else if ( a.hashCode != b.hashCode ) false
      else if ( a.getClass != b.getClass ) false
      else if ( areEqual contains PtrPair( a, b ) ) true
      else if ( a.productArity != b.productArity ) false
      else {
        val allElementsEqual = ( a.productIterator zip b.productIterator ) forall {
          case ( a1: DagProof[_], b1: DagProof[_] ) => checkEqual( a1, b1 )
          case ( a1, b1 )                           => a1 == b1
        }

        if ( allElementsEqual ) {
          areEqual += PtrPair( a, b )
          true
        } else {
          false
        }
      }

    that match {
      case that: DagProof[_] => checkEqual( this, that )
      case _                 => false
    }
  }

}
