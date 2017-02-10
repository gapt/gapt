package at.logic.gapt.proofsNew

import scala.collection.mutable

trait Inference[+Jdg] {
  def premises: Vector[Jdg]
  def conclusion: Jdg

  def name: String = longName
  def longName: String = getClass.getSimpleName
}

/**
 * DAG-like proof.
 *
 * Proofs are recursive structures that are represented as case classes.  Equality is standard case class equality
 * (but implemented in such a way that it is efficient on DAGs).
 */
final class DagProof[Jdg, +Inf <: Inference[Jdg]]( val inference: Inf, val immediateSubProofs: Vector[DagProof[Jdg, Inf]] ) { self =>
  require(
    inference.premises.size == immediateSubProofs.size,
    s"Inference has ${inference.premises.size} premises, but ${immediateSubProofs.size} sub-proofs were provided."
  )
  for ( ( premise, subProof ) <- ( inference.premises, immediateSubProofs ).zipped )
    require( premise == subProof.conclusion )

  /**
   * The name of this rule (in symbols).
   */
  def name: String = inference.name

  /**
   * The name of this rule (in words).
   */
  def longName: String = inference.longName

  /** Operations that view the sub-proofs as a tree, see [[DagProof.TreeLikeOps]] for a list. */
  def treeLike = new DagProof.TreeLikeOps( self )

  /** Operations that view the sub-proofs as a DAG, which ignore duplicate sub-proofs, see [[DagProof.DagLikeOps]] for a list. */
  def dagLike = new DagProof.DagLikeOps( self )

  /**
   * Set of all (transitive) sub-proofs including this.
   */
  def subProofs[Inf_ >: Inf <: Inference[Jdg]]: Set[DagProof[Jdg, Inf_]] = dagLike foreach { _ => () }

  def map[Jdg_, Inf_ <: Inference[Jdg_]]( f: Inf => Inf_ ): DagProof[Jdg_, Inf_] = {
    val cache = mutable.Map[DagProof[Jdg, Inf], DagProof[Jdg_, Inf_]]()
    def go( p: DagProof[Jdg, Inf] ): DagProof[Jdg_, Inf_] = cache.getOrElse(
      p,
      DagProof( f( p.inference ), p.immediateSubProofs.map( go ) )
    )
    go( this )
  }

  def flatMap[Jdg_, Inf_ <: Inference[Jdg_]]( f: Inf => Traversable[Inf_] ): DagProof[Jdg_, Inf_] = {
    var builder = new DagProofBuilder[Jdg_, Inf_]
    for ( p <- treeLike.postOrder; inf_ <- f( p.inference ) )
      builder = builder.c( inf_ )
    builder.qed
  }

  def collect[Jdg_, Inf_ <: Inference[Jdg_]]( f: PartialFunction[Inf, Inf_] ): DagProof[Jdg_, Inf_] =
    flatMap[Jdg_, Inf_]( inf => if ( f.isDefinedAt( inf ) ) List( f( inf ) ) else Nil )

  def weakenJudgments[Jdg_ >: Jdg]: DagProof[Jdg_, Inf] =
    asInstanceOf[DagProof[Jdg_, Inf]]

  /**
   * Returns the subproof at the given position: p.subProofAt(Nil) is p itself; p.subProofAt(i :: is) is the ith
   * subproof of p.subProofAt(is).
   */
  def subProofAt( pos: List[Int] ): DagProof[Jdg, Inf] = pos match {
    case Nil => this
    case i :: is =>
      val sub = subProofAt( is )
      require( sub.immediateSubProofs isDefinedAt i, s"Proof $sub does not have an immediate subproof with index $i." )
      sub.immediateSubProofs( i )
  }

  /**
   * Depth of the proof, which is the maximum length of a path you can take via [[immediateSubProofs]].
   */
  def depth: Int = {
    val memo = mutable.Map[DagProof[Jdg, Inf], Int]()
    def f( subProof: DagProof[Jdg, Inf] ): Int = memo.getOrElseUpdate(
      subProof,
      ( subProof.immediateSubProofs.map( f ) :+ 0 ).max + 1
    )
    f( this )
  }

  def conclusion: Jdg = inference.conclusion

  override def toString: String = dagLike.toString

  override val hashCode: Int = inference.hashCode ^ immediateSubProofs.hashCode

  override def equals( that: Any ): Boolean =
    that match {
      case that: DagProof[j, i] => eq( that ) || DagProof.equal[Jdg, Inf, j, i]( this, that )
      case _                    => false
    }

}

object DagProof {
  def apply[Jdg, Inf <: Inference[Jdg]]( inf: Inf, premises: Vector[DagProof[Jdg, Inf]] ): DagProof[Jdg, Inf] =
    new DagProof( inf, premises )

  def apply[Jdg, Inf <: Inference[Jdg]]( inf: Inf, premises: DagProof[Jdg, Inf]* ): DagProof[Jdg, Inf] =
    DagProof( inf, premises.toVector )

  def unapplySeq[Jdg, Inf <: Inference[Jdg]]( proof: DagProof[Jdg, Inf] ): Option[( Inf, Seq[DagProof[Jdg, Inf]] )] =
    Some( ( proof.inference, proof.immediateSubProofs ) )

  def equal[Jdg1, Inf1 <: Inference[Jdg1], Jdg2, Inf2 <: Inference[Jdg2]]( a: DagProof[Jdg1, Inf1], b: DagProof[Jdg2, Inf2] ): Boolean = {
    case class PtrPair( a: DagProof[Jdg1, Inf1], b: DagProof[Jdg2, Inf2] ) {
      override def hashCode = 31 * System.identityHashCode( a ) + System.identityHashCode( b )
      override def equals( that: Any ) = that match {
        case PtrPair( a_, b_ ) => ( a eq a_ ) && ( b eq b_ )
        case _                 => false
      }
    }

    val areEqual = mutable.Set[PtrPair]()
    def checkEqual( a: DagProof[Jdg1, Inf1], b: DagProof[Jdg2, Inf2] ): Boolean =
      if ( a eq b ) true
      else if ( a.hashCode != b.hashCode ) false
      else if ( a.getClass != b.getClass ) false
      else if ( areEqual contains PtrPair( a, b ) ) true
      else if ( a.inference != b.inference ) false
      else if ( a.immediateSubProofs.size != b.immediateSubProofs.size ) false
      else {
        if ( ( a.immediateSubProofs, b.immediateSubProofs ).zipped.forall( checkEqual ) ) {
          areEqual += PtrPair( a, b )
          true
        } else {
          false
        }
      }

    checkEqual( a, b )
  }

  class TreeLikeOps[Jdg, +Inf <: Inference[Jdg]]( val self: DagProof[Jdg, Inf] ) extends AnyVal {

    /**
     * Iterate over all sub-proofs including this in post-order.
     */
    def foreach( f: DagProof[Jdg, Inf] => Unit ): Unit = {
      for ( p <- self.immediateSubProofs ) p.treeLike foreach f
      f( self )
    }

    /**
     * A sequence of all sub-proofs including this in post-order.
     */
    def postOrder: Seq[DagProof[Jdg, Inf]] = {
      val subProofs = Seq.newBuilder[DagProof[Jdg, Inf]]
      for ( p <- self.treeLike ) subProofs += p
      subProofs.result()
    }

    /**
     * Number of sub-proofs including this, counting duplicates.
     */
    def size: BigInt = {
      val memo = mutable.Map[DagProof[Jdg, Inf], BigInt]()
      def f( subProof: DagProof[Jdg, Inf] ): BigInt =
        memo.getOrElseUpdate(
          subProof,
          subProof.immediateSubProofs.map( f ).sum + 1
        )
      f( self )
    }

    override def toString: String = {
      val output = Seq.newBuilder[String]
      var number = 0
      def write( step: DagProof[Jdg, Inf] ): ( Any, String ) = {
        val subProofLabels = step.immediateSubProofs.map( write ).toMap
        number += 1
        val label = s"p$number"
        output += s"[$label] ${step.conclusion} (${step.immediateSubProofs.map( subProofLabels( _ ) + ", " ).mkString}${step.inference})\n"
        step -> label
      }
      write( self )
      output.result().reverse.mkString
    }
  }

  class DagLikeOps[Jdg, +Inf <: Inference[Jdg]]( val self: DagProof[Jdg, Inf] ) extends AnyVal {

    /**
     * Iterate over all sub-proofs including this in post-order, ignoring duplicates.
     * @return Set of all visited sub-proofs including this.
     */
    def foreach[Inf_ >: Inf <: Inference[Jdg]]( f: DagProof[Jdg, Inf] => Unit ): Set[DagProof[Jdg, Inf_]] = {
      val seen = mutable.Set[DagProof[Jdg, Inf]]()

      def traverse( p: DagProof[Jdg, Inf] ): Unit =
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
    def postOrder: Seq[DagProof[Jdg, Inf]] = {
      val subProofs = Seq.newBuilder[DagProof[Jdg, Inf]]
      for ( p <- self.dagLike ) subProofs += p
      subProofs.result()
    }

    /**
     * A sequence of all sub-proofs including this in post-order, ignoring duplicates.
     */
    def breadthFirst: Seq[DagProof[Jdg, Inf]] = {
      val seen = mutable.Set[DagProof[Jdg, Inf]]()
      val result = Seq.newBuilder[DagProof[Jdg, Inf]]
      val queue = mutable.Queue[DagProof[Jdg, Inf]]( self )

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
    def size: Int = self.subProofs.size

    override def toString: String = {
      val steps = self.dagLike.postOrder.zipWithIndex map { case ( p, i ) => ( p, s"p${i + 1}" ) }
      val subProofLabels: Map[Any, String] = steps.toMap

      val output = new StringBuilder()
      steps.reverse foreach {
        case ( step, label ) =>
          output ++= s"[$label] ${step.conclusion} (${step.immediateSubProofs.map( subProofLabels( _ ) + ", " ).mkString}${step.inference})\n"
      }
      output.result()
    }
  }
}
