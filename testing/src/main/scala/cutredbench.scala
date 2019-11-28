package gapt.testing
import gapt.cutintro.CutIntroduction
import gapt.examples._
import gapt.expr._
import gapt.expr.fol.Numeral
import gapt.expr.hol.{ containsQuantifierOnLogicalLevel, isAtom }
import gapt.proofs.HOLSequent
import gapt.proofs.ceres.CERES
import gapt.proofs.expansion.{ ExpansionProof, eliminateCutsET }
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.lk.transformations.eliminateDefinitions
import gapt.proofs.lk.transformations.inductionNormalForm
import gapt.proofs.lk.util.instanceProof
import gapt.proofs.lk.{ LKProof, normalizeLKt }
import gapt.proofs.lkt.{ LKToLKt, LKt, LocalCtx }
import gapt.proofs.resolution.ResolutionToLKProof
import gapt.provers.escargot.Escargot

import scala.concurrent.duration._

object CutReductionBenchmarkTools {
  def measure( f: => Unit ): Duration = {
    val begin = System.nanoTime()
    f
    val end = System.nanoTime()
    ( end - begin ).nanos
  }

  def robustlyMeasure( f: => Unit ): Duration = {
    val time0 = measure( f )
    val extraRuns =
      math.max( 0, math.min(
        math.max( 2, math.round( 1.second / time0 ) ),
        math.floor( 10.seconds / time0 ).toLong ) )
    val time1 = measure( ( 0L until extraRuns ).foreach( _ => f ) )
    ( time0 + time1 ) / ( 1 + extraRuns )
  }

  trait Method {
    type P
    def convert( p: LKProof ): P
    def eliminate( p: P ): Unit
    def robustlyMeasureElimination( lk: LKProof ): Duration = {
      val p = convert( lk )
      robustlyMeasure( eliminate( p ) )
    }
  }
  trait LKMethod extends Method {
    type P = LKProof
    def convert( p: LKProof ): P = p
  }
  case object LKReductive extends LKMethod { def eliminate( p: LKProof ): Unit = cutNormal( p ) }
  case object LKCERES extends LKMethod { def eliminate( p: LKProof ): Unit = CERES( p ) }
  case object CERESEXP extends LKMethod { def eliminate( p: LKProof ): Unit = CERES.expansionProof( p ) }
  case object BogoElim extends Method {
    type P = HOLSequent
    def convert( p: LKProof ): P = p.endSequent
    def eliminate( p: P ): Unit = Escargot.getExpansionProof( p ).get
  }
  case object ExpCutElim extends Method {
    type P = ExpansionProof
    def convert( p: LKProof ): P = LKToExpansionProof( p )
    def eliminate( p: P ): Unit = eliminateCutsET( p )
  }
  class AbstractLKtNorm( skipCut: Formula => Boolean = _ => false ) extends Method {
    type P = LKt
    def convert( p: LKProof ): P = LKToLKt( p )._1
    def eliminate( p: LKt ): Unit = normalizeLKt( p, skipCut )
  }
  case object LKtNorm extends AbstractLKtNorm
  case object LKtNormA extends AbstractLKtNorm( isAtom( _ ) )
  case object LKtNormP extends AbstractLKtNorm( !containsQuantifierOnLogicalLevel( _ ) )
  val methods = List( LKReductive, LKCERES, CERESEXP, BogoElim, ExpCutElim, LKtNorm, LKtNormA, LKtNormP )
}

object cutReductionBenchmark extends Script {
  import CutReductionBenchmarkTools._

  def turnEqualityIntoPredicate[A: ClosedUnderReplacement]( a: A ): A =
    TermReplacement( a, { case EqC( t ) => Const( "E", t ->: t ->: To ) } )

  // warmup
  for ( m <- methods ) m.robustlyMeasureElimination( LinearCutExampleProof( 3 ) )

  println( "proof,n," + methods.mkString( "," ) )

  def bench( name: String, n: Int, lk: LKProof, exclude: Set[Method] = Set() ): Unit = {
    val times = methods.map {
      case m if exclude( m ) => "NaN"
      case m                 => m.robustlyMeasureElimination( lk ).toUnit( SECONDS ).toString
    }
    println( s"$name,$n," + times.mkString( "," ) )
  }

  bench( "pi2pigeon", -1, Pi2Pigeonhole.proof )
  bench( "pi3pigeon", -1, Pi3Pigeonhole.proof )

  {
    import gapt.examples.lattice._
    bench( "lattice", -1, eliminateDefinitions( p ), exclude = Set( LKReductive, BogoElim ) )
  }

  for ( n <- 0 to 18; p <- CutIntroduction( LinearEqExampleProof( n ) ) )
    bench( "ci_lineareq", n, turnEqualityIntoPredicate( p ) )
  for ( n <- 0 to 18; p <- CutIntroduction( LinearExampleProof( n ) ) ) bench( "ci_linear", n, p )
  for ( n <- 0 to 18; p <- CutIntroduction( SquareDiagonalExampleProof( n ) ) ) bench( "ci_sqdiag", n, p )
  for ( n <- 0 to 5; p <- CutIntroduction( FactorialFunctionEqualityExampleProof( n ) ) )
    bench( "ci_fact", n, turnEqualityIntoPredicate( p ), exclude = Set( BogoElim ) )

  for ( n <- 0 to 10 ) {
    val Some( res ) = Escargot.getResolutionProof( fof"P(0) & !x (P(x) -> P(s(x))) -> P${Numeral( n )}" )
    val lk = ResolutionToLKProof( res )
    bench( "linearacnf", n, lk )
  }

  for ( n <- 0 to 8 ) bench( "linear", n, LinearCutExampleProof( n ) )
}

object primeCutElimBench extends Script {
  import CutReductionBenchmarkTools._

  def furstenbergProof( n: Int ): LKProof = {
    import gapt.proofs.lkt._
    val primeInst = gapt.examples.prime.furstenberg( n )
    import primeInst._
    val p0 = eliminateDefinitions( proof )
    val ( p1, lctx ) = LKToLKt( p0 )
    val p2 = atomizeEquality( p1, lctx )
    LKtToLK( p2, lctx )
  }

  val lktMethods = List( LKtNorm, LKtNormA, LKtNormP )
  // warmup
  for ( m <- lktMethods ) m.robustlyMeasureElimination( LinearCutExampleProof( 3 ) )

  println( "n," + lktMethods.mkString( "," ) )
  for ( i <- 0 to 9 ) {
    val p = furstenbergProof( i )
    val times = lktMethods.map( _.robustlyMeasureElimination( p ).toUnit( SECONDS ).toString )
    println( s"$i," + times.mkString( "," ) )
  }
}

object indElimBench extends Script {
  import gapt.examples.theories._
  object AllTheories extends Theory(
    logic, set, props, nat, natdivisible, natdivision, natorder, list, listlength, listfold, listdrop, natlists, fta )
  import AllTheories._
  import CutReductionBenchmarkTools._

  class AbstractIndLKtNorm( skipCut: Formula => Boolean = _ => false ) extends Method {
    type P = ( LKt, LocalCtx )
    def convert( p: LKProof ): P = LKToLKt( p )
    def eliminate( p: ( LKt, LocalCtx ) ): Unit =
      normalizeLKt.induction( p._1, p._2, skipCut = skipCut )
  }
  case object IndLKtNorm extends AbstractIndLKtNorm
  case object IndLKtNormA extends AbstractIndLKtNorm( isAtom( _ ) )
  case object IndLKtNormP extends AbstractIndLKtNorm( !containsQuantifierOnLogicalLevel( _ ) )
  case object IndLKReductive extends LKMethod {
    def eliminate( p: LKProof ): Unit = inductionNormalForm( p )
  }
  case object BogoElim extends Method {
    // TODO: remove once context guessing works
    type P = HOLSequent
    def convert( p: LKProof ): P = p.endSequent
    def eliminate( p: P ): Unit = {
      implicit val mctx = ctx.newMutable
      Escargot.getExpansionProof( p ).get
    }
  }

  val indMethods = Seq( IndLKReductive, BogoElim, IndLKtNorm, IndLKtNormA, IndLKtNormP )

  def mkNum( n: Int ): Expr = if ( n == 0 ) le"0" else le"s ${mkNum( n - 1 )}"
  def mkList( n: Int, x: String ): Expr = if ( n == 0 ) le"nil:list ?a" else le"cons ${Var( s"${x}n", ty"?a" )} ${mkList( n - 1, x )}"

  def benchn( name: String, lk: LKProof, n: Int, exclude: Set[Method] = Set() ): Unit = {
    val times = indMethods.map {
      case m if exclude( m ) => "NaN"
      case m                 => m.robustlyMeasureElimination( lk ).toUnit( SECONDS ).toString
    }
    println( s"$name,$n," + times.mkString( "," ) )
  }
  def bench( name: String, terms: Seq[Seq[Expr]], exclude: Set[Method] = Set() ): Unit = {
    val hnd = LemmaHandle( name )
    val p = hnd.combined()
    for ( ( ts, i ) <- terms.zipWithIndex ) benchn( hnd.name, instanceProof( p, ts ), i, exclude )
  }
  println( "proof,n," + indMethods.mkString( "," ) )

  // warmup
  {
    val p = instanceProof( LemmaHandle( "add0l" ).combined(), mkNum( 2 ) )
    for ( m <- indMethods ) m.robustlyMeasureElimination( p )
  }

  bench( "filterrev", for ( i <- 0 to 4 ) yield Seq( le"P:?a>o", mkList( i, "x" ) ), exclude = Set( IndLKReductive ) )
  bench( "primedecex", for ( i <- 0 to 2 ) yield Seq( mkNum( i ) ), exclude = Set( IndLKReductive, BogoElim ) )
  bench( "divmodgtot", for ( i <- 0 to 3 ) yield Seq( mkNum( i ) ), exclude = Set( IndLKReductive, BogoElim ) )
  bench( "ltirrefl", for ( i <- 0 to 10 ) yield Seq( mkNum( i ) ), exclude = Set( IndLKReductive, BogoElim ) )
  bench( "mul1", for ( i <- 0 to 15 ) yield Seq( mkNum( i ) ) )
  bench( "add0l", for ( i <- 0 to 15 ) yield Seq( mkNum( i ) ) )
}