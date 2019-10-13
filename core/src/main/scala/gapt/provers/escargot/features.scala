package gapt.provers.escargot.impl

import gapt.expr._
import gapt.expr.subst.PreSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.util.syntacticMatching
import gapt.proofs.{ HOLSequent, Sequent }

class FrequenciesBuilder( private var arr: Array[Int] = new Array[Int]( Frequencies.buckets ) ) {
  def increment( f: String ): Unit =
    arr( f.hashCode & Frequencies.bucketMask ) += 1

  def +=( that: Frequencies ): Unit =
    for ( i <- 0 until Frequencies.buckets ) arr( i ) += that( i )

  def result(): Frequencies = {
    val res = new Frequencies( arr )
    arr = null
    res
  }
}

class Frequencies( private val arr: Array[Int] ) extends AnyVal {
  def apply( i: Int ): Int = arr( i & Frequencies.bucketMask )

  def <=( that: Frequencies ): Boolean = {
    var i = 0
    while ( i < Frequencies.buckets ) {
      if ( this.arr( i ) > that.arr( i ) )
        return false
      i += 1
    }
    true
  }
}
object Frequencies {
  val buckets = 32
  val bucketMask = buckets - 1
}

case class TermFeatureVec(
    depth:      Int,
    numConsts:  Int,
    freqConsts: Frequencies ) {
  def fast_<=( that: TermFeatureVec ): Boolean =
    this.depth <= that.depth && this.numConsts <= that.numConsts

  def <=( that: TermFeatureVec ): Boolean =
    this.fast_<=( that ) && this.freqConsts <= that.freqConsts
}

object TermFeatureVec {
  def apply( e: Expr ): TermFeatureVec = {
    var depth = 0
    var numConsts = 0
    val freqConsts = new FrequenciesBuilder
    def gather( e: Expr, d: Int ): Unit = {
      if ( d > depth ) depth = d
      e match {
        case App( a, b ) =>
          gather( a, d )
          gather( b, d + 1 )
        case Var( _, _ ) | Abs( _, _ ) =>
        case Const( n, _, _ ) =>
          numConsts += 1
          freqConsts.increment( n )
      }
    }
    gather( e, 0 )
    TermFeatureVec( depth, numConsts, freqConsts.result() )
  }

  def union( fvs: Iterable[TermFeatureVec] ): TermFeatureVec = {
    var depth = 0
    var numConsts = 0
    val freqConsts = new FrequenciesBuilder
    for ( fv <- fvs ) {
      depth = math.max( depth, fv.depth )
      numConsts += fv.numConsts
      freqConsts += fv.freqConsts
    }
    TermFeatureVec( depth, numConsts, freqConsts.result() )
  }
}

case class ClauseFeatureVec(
    numLitsNeg: Int,
    numLitsPos: Int,
    featNeg:    TermFeatureVec,
    featPos:    TermFeatureVec ) {
  def <=( that: ClauseFeatureVec ): Boolean =
    this.numLitsNeg <= that.numLitsNeg && this.numLitsPos <= that.numLitsPos &&
      this.featNeg.fast_<=( that.featNeg ) && this.featPos.fast_<=( that.featPos ) &&
      this.featNeg <= that.featNeg && this.featPos <= that.featPos
}

object ClauseFeatureVec {
  def apply( cls: HOLSequent )( implicit dummyImplicit: DummyImplicit ): ClauseFeatureVec =
    ClauseFeatureVec( cls.map( TermFeatureVec( _ ) ) )

  def apply( cls: Sequent[TermFeatureVec] ): ClauseFeatureVec =
    ClauseFeatureVec( cls.antecedent.size, cls.succedent.size,
      TermFeatureVec.union( cls.antecedent ), TermFeatureVec.union( cls.succedent ) )
}

object fastSubsumption {
  def apply( c1: HOLSequent, c2: HOLSequent,
             fv1: ClauseFeatureVec, fv2: ClauseFeatureVec,
             lfv1: Sequent[TermFeatureVec], lfv2: Sequent[TermFeatureVec] ): Option[Substitution] = {
    if ( !( fv1 <= fv2 ) ) return None
    if ( c1.sizes == ( 1, 0 ) ) {
      val l1 = c1.antecedent.head
      val lf1 = lfv1.antecedent.head
      return c2.antecedent.lazyZip( lfv2.antecedent ).view.
        filter( lf1 <= _._2 ).map( _._1 ).flatMap( syntacticMatching( l1, _ ) ).headOption
    }
    if ( c1.sizes == ( 0, 1 ) ) {
      val l1 = c1.succedent.head
      val lf1 = lfv1.succedent.head
      return c2.succedent.lazyZip( lfv2.succedent ).view.
        filter( lf1 <= _._2 ).map( _._1 ).flatMap( syntacticMatching( l1, _ ) ).headOption
    }
    apply( c1 zip lfv1, c2 zip lfv2, PreSubstitution() )
  }

  def apply(
    from:  Sequent[( Expr, TermFeatureVec )],
    to:    Sequent[( Expr, TermFeatureVec )],
    subst: PreSubstitution ): Option[Substitution] = {
    if ( from isEmpty ) return Some( subst.toSubstitution )
    val chosenFrom = from.indices.head
    val ( fromExpr, fromFV ) = from( chosenFrom )
    ( for {
      chosenTo <- to.indices.view
      if chosenTo sameSideAs chosenFrom
      ( toExpr, toFV ) = to( chosenTo )
      if fromFV <= toFV
      newSubst <- syntacticMatching( fromExpr, toExpr, subst )
      subsumption <- apply( from delete chosenFrom, to delete chosenTo, newSubst )
    } yield subsumption ).headOption
  }
}
