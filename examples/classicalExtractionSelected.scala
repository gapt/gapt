package gapt.examples

import extraction.ScalaCodeGenerator
import gapt.expr._
import gapt.expr.hol.{CNFn, CNFp}
import gapt.formats.babel._
import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.context.Context
import gapt.proofs.{Ant, ProofBuilder}
import gapt.proofs.context.update.{InductiveType, PrimitiveRecursiveFunction}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.transformations.LKToND
import gapt.proofs.nd._
import gapt.proofs.resolution.PCNF
import gapt.prooftool.prooftool
import gapt.provers.smtlib.Z3
import gapt.utils.LogHandler

object sqrtProofManualCorrectAxiom extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.nd._

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  implicit var cctx = ClassicalExtraction.systemT( ctx )
  val Some( z ) = cctx.constant( "0" )
  val Some( s ) = cctx.constant( "s" )
  val Some( gt ) = cctx.constant( "gt" )
  //val Some( not ) = cctx.constant( "not" )
  val not = hoc"'not': o>o"
  cctx += PrimitiveRecursiveFunction(
    not,
    List(
      ( not( hof"true" ) -> hof"false" ),
      ( not( hof"false" ) -> hof"true" ) ) )( cctx )

  val x = hov"x:nat"
  val y = hov"y:nat"
  val plus = hoc"'+': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    plus,
    List(
      ( plus( z, y ) -> y ),
      ( plus( s( x ), y ) -> s( plus( x, y ) ) ) ) )( cctx )
  val times = hoc"'*': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    times,
    List(
      ( times( z, y ) -> z ),
      ( times( s( x ), y ) -> plus( y, times( x, y ) ) ) ) )( cctx )
  val lt = hoc"'<': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    lt,
    List(
      ( lt( z, y ) -> gt( y, z ) ),
      ( lt( s( x ), y ) -> gt( y, s( x ) ) ) ) )( cctx )
  val leq = hoc"'<=': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    leq,
    List(
      ( leq( z, y ) -> not( gt( z, y ) ) ),
      ( leq( s( x ), y ) -> not( gt( s( x ), y ) ) ) ) )( cctx )
  println( s"normalize 0 > 1: ${normalize( gt( z, s( z ) ) )}" )
  println( s"normalize 0 > 0: ${normalize( gt( z, z ) )}" )
  println( s"normalize 1 > 0: ${normalize( gt( s( z ), z ) )}" )
  println( s"normalize 1 > 1: ${normalize( gt( s( z ), s( z ) ) )}" )
  println( s"normalize 0 < 1: ${normalize( lt( z, s( z ) ) )}" )
  println( s"normalize 1 < 1: ${normalize( lt( s( z ), s( z ) ) )}" )
  println( s"normalize 1 < 0: ${normalize( lt( s( z ), z ) )}" )
  println( s"normalize 0 <= 1: ${normalize( leq( z, s( z ) ) )}" )
  println( s"normalize 1 <= 1: ${normalize( leq( s( z ), s( z ) ) )}" )
  println( s"normalize 2 <= 1: ${normalize( leq( s( s( z ) ), s( z ) ) )}" )
  println( s"normalize 0 * 0: ${normalize( times( z, z ) )}" )
  println( s"normalize 0 * 1: ${normalize( times( z, s( z ) ) )}" )
  println( s"normalize 1 * 0: ${normalize( times( s( z ), z ) )}" )
  println( s"normalize 2 * 2: ${normalize( times( s( s( z ) ), s( s( z ) ) ) )}" )

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val minorLem1 = hof"s(n) = s(y0) * s(y0)"
  val minorLem2 = hof"s(n) < s(y0) * s(y0)"
  val minorLem3 = hof"y0 * y0 < n"
  val minorLem4 = hof"n < s(y0) * s(y0) & y0 * y0 <= n"
  val minorLem5 = hof"y0 * y0 = n"
  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( minorLem1 ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( minorLem2 ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( minorLem3 ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( minorLem4 ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( minorLem1 ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( minorLem1 ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( minorLem2 ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( minorLem5 ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( minorLem4 ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( minorLem4 ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, minorLem4 ) ).
    u( ContractionRule( _, minorLem4 ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val icStep = InductionCase( step, hoc"s", List( step.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )

  import scala.collection._
  def assignArgs( prog: Expr, args: mutable.Map[Ty, Expr] ): Expr = prog.ty match {
    case TArr( TBase( "nat", _ ), _ ) | TBase( "conj", _ ) => prog
    case TArr( argTy, _ ) =>
      val arg = args( argTy )
      println( s"assigning $arg to ${prog.ty}" )
      assignArgs( prog( arg ), args )
  }
  val progArgs = mutable.Map[Ty, Expr](
    List( trans, lem3, lem4, lem5, symm, lem7, peano1, peano2, lem8, D0, Dn, Dsn, minorLem1, minorLem2, minorLem3, minorLem4, minorLem5 ).zipWithIndex.map {
      case ( f, i ) => ClassicalExtraction.flat( f ) -> Const( s"arg$i", ClassicalExtraction.flat( f ) )
    }: _* )

  val Some( i ) = cctx.constant( "i" )
  val Some( ite ) = cctx.constant( "ite", List( ty"sum(1)(1)" ) )
  val Some( pair ) = cctx.constant( "pair", List( ty"1>sum(1)(1)", ty"sum(1)(1)>1" ) )
  val Some( cmp ) = cctx.constant( "cmp" )
  val Some( cmp2 ) = cctx.constant( "cmp2" )
  val Some( inl ) = cctx.constant( "inl", List( ty"1", ty"1" ) )
  val Some( inr ) = cctx.constant( "inr", List( ty"1", ty"1" ) )
  val Some( proj1 ) = cctx.constant( "pi1", List( ty"nat", ty"conj(1)(1)" ) )
  //(x < y -> (s(x) = y | s(x) < y))"
  progArgs += ( ClassicalExtraction.flat( lem1 ) ->
    le"""
  (^(tmp1:nat) (^(tmp2:nat) (^(tmp3:1) ($ite($lt($s(tmp1), tmp2))($inr($i))($inl($i))))))
  """ )
  // (x<=y <-> (x=y | x<y))"
  progArgs += ( ClassicalExtraction.flat( defleq ) ->
    le"""(^(tmp3:nat) (^(tmp4:nat)
  $pair(
    (^(tmp5:1) ($cmp2 tmp3 tmp4)),
    (^(tmp6:sum(1)(1)) $i)
  )))""" )
  //import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  val realm1 = assignArgs( m1, progArgs )
  println(realm1.toUntypedString)
  //ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
  //println( normalize( proj1( realm1( le"s(s(s(s(0))))" ) ) ) )
  //println( normalize( proj1( realm1( le"s(s(0))" ) ) ) )

  /*
  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
  */
}

object manualExistsMinimumNoDefinitions extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += Notation.Infix( "+", Precedence.plusMinus )

  implicit var cctx = ClassicalExtraction.systemT( ctx )

  val Some( z ) = cctx.constant( "0" )
  val Some( s ) = cctx.constant( "s" )
  val Some( subtr ) = cctx.constant( "subtr" )
  val Some( ite ) = cctx.constant( "ite", List( ty"nat" ) )
  val Some( gt ) = cctx.constant( "gt" )
  val Some( not ) = cctx.constant( "not" )

  val x = hov"x:nat"
  val y = hov"y:nat"
  // def f( x: Int ) = if ( x > 1 ) 0 else 1 - x
  // min at x = 1
  val f = hoc"'f': nat>nat"
  cctx += PrimitiveRecursiveFunction(
    f,
    List(
      ( f( z ) -> subtr( s( z ), z ) ),
      ( f( s( x ) ) -> ite( gt( s( x ), s( z ) ) )( z )( subtr( s( z ), s( x ) ) ) ) ) )( cctx )
  val plus = hoc"'+': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    plus,
    List(
      ( plus( z, y ) -> y ),
      ( plus( s( x ), y ) -> s( plus( x, y ) ) ) ) )( cctx )
  val lt = hoc"'<': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    lt,
    List(
      ( lt( z, y ) -> gt( y, z ) ),
      ( lt( s( x ), y ) -> gt( y, s( x ) ) ) ) )( cctx )
  val leq = hoc"'<=': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    leq,
    List(
      ( leq( z, y ) -> not( gt( z, y ) ) ),
      ( leq( s( x ), y ) -> not( gt( s( x ), y ) ) ) ) )( cctx )

  println( s"normalize 0 - 0: ${normalize( subtr( z, z ) )}" )
  println( s"normalize 1 - 0: ${normalize( subtr( s( z ), z ) )}" )
  println( s"normalize 0 - 1: ${normalize( subtr( z, s( z ) ) )}" )
  println( s"normalize 2 - 1: ${normalize( subtr( s( s( z ) ), s( z ) ) )}" )

  val lem1 = hof"!x!y (x < s(y) -> x <= y)"
  val lem2 = hof"!x (x <= 0 -> x = 0)"
  val lem3 = hof"!y (y = 0 -> -(?x f(x) < y))"
  val lem4 = hof"!x (x <= x)"
  val lem5 = hof"-(?x (f(x) < s(n)))"
  val lem6 = hof"?x (f(x) <= s(n))"
  val lem7 = hof"?x (f(x) < s(n))"
  val lem8 = hof"(?x (f(x) <= n)) -> (?y ((-(?x (f(x) < y))) & (?x (f(x) <= y))))"
  val lem9 = hof"f(x) < s(n)"
  val lem10 = hof"?x (f(x) <= 0)"
  val lem11 = hof"f(z) <= 0"
  val lem12 = hof"f(0) <= f(0)"

  val T1 = ProofBuilder.
    c( LogicalAxiom( lem5 ) ).
    c( LogicalAxiom( lem6 ) ).
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?y ((-(?x (f(x) < y))) & (?x (f(x) <= y)))" ) ).
    qed
  //prooftool( T1 )

  val T2 = ProofBuilder.
    c( LogicalAxiom( lem7 ) ).
    c( LogicalAxiom( lem8 ) ).
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"f(x)", le"(n:nat)" ) ) ).
    c( LogicalAxiom( lem9 ) ).
    b( ImpElimRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= n)" ) ).
    b( ImpElimRule( _, _ ) ).
    b( ExistsElimRule( _, _ ) ).
    qed
  //prooftool( T2 )

  val step = ProofBuilder.
    c( T2 ).
    c( T1 ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ImpIntroRule( _, hof"?x (f(x) <= s(n))" ) ).
    //u( ImpIntroRule( _, hof"lesseqf(n) -> hasminf" ) ).
    //u( ForallIntroRule( _, hof"!n ((lesseqf(n) -> hasminf) -> (lesseqf(s(n)) -> hasminf))", hov"(n:nat)" ) ).
    qed
  //prooftool( step )
  val icStep = InductionCase( step, hoc"s", List( step.endSequent.indexOfInAnt( hof"(?x (f(x) <= n)) -> (?y ((-(?x (f(x) < y))) & (?x (f(x) <= y))))" ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( lem10 ) ).
    c( LogicalAxiom( lem3 ) ).
    u( ForallElimRule( _, le"f(z)" ) ).
    c( LogicalAxiom( lem2 ) ).
    u( ForallElimRule( _, le"f(z)" ) ).
    c( LogicalAxiom( lem11 ) ).
    b( ImpElimRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"f(z)" ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= f(z))" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?y ((-(?x (f(x) < y))) & (?x (f(x) <= y)))" ) ).
    b( ( pl, pr ) => ExistsElimRule( pl, pr, pr.endSequent.indexOfInAnt( hof"f(z) <= 0" ), hov"z:nat" ) ).
    u( ImpIntroRule( _, hof"?x (f(x) <= 0)" ) ).
    qed
  //prooftool( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", hof"(?x (f(x) <= n)) -> (?y ((-(?x (f(x) < y))) & (?x (f(x) <= y))))" ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ForallElimRule( _, le"f(0)" ) ).
    c( LogicalAxiom( lem12 ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= f(0))" ) ).
    b( ImpElimRule( _, _ ) ).
    qed
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  //ScalaCodeGenerator( "hasmin" )( m1 )( ClassicalExtraction.systemT( ctx ) )

  import scala.collection._
  def assignArgs( prog: Expr, args: mutable.Map[Ty, Expr] ): Expr = prog.ty match {
    case TArr( TBase( "nat", _ ), _ ) | TBase( "conj", _ ) => prog
    case TArr( argTy, _ ) =>
      val arg = args( argTy )
      println( s"assigning $arg to ${prog.ty}" )
      assignArgs( prog( arg ), args )
  }

  val m1Args = mutable.Map[Ty, Expr](
    List( lem1, lem2, lem3, lem4, lem5, lem6, lem7, lem8, lem9, lem10, lem11, lem12 ).zipWithIndex.map {
      case ( f, i ) => ClassicalExtraction.flat( f ) -> Const( s"arg$i", ClassicalExtraction.flat( f ) )
    }: _* )

  val realm1 = assignArgs( m1, m1Args )

  // Constructive proof
  val lem13 = hof"!x!y (-(x < y) -> (y <= x))"
  val lem14 = hof"-(?x (f(x) < y))"
  val lem15 = hof"f(x) < y"
  val lem19 = ProofBuilder.
    c( LogicalAxiom( lem13 ) ).
    u( ForallElimBlock( _, List( le"f(x)", le"y:nat" ) ) ).
    c( LogicalAxiom( lem14 ) ).
    c( LogicalAxiom( lem15 ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) < y)" ) ).
    b( NegElimRule( _, _ ) ).
    u( NegIntroRule( _, hof"f(x) < y" ) ).
    b( ImpElimRule( _, _ ) ).
    u( ForallIntroRule( _, hov"x:nat", hov"x:nat" ) ).
    u( ImpIntroRule( _, hof"-(?x (f(x) < y))" ) ).
    u( ForallIntroRule( _, hov"y:nat", hov"y:nat" ) ).
    qed

  /*
// Classical proof
// TODO: add lem16 to args list when using classical proof
val lem13 = hof"y <= f(x)"
val lem14 = hof"-(?x (f(x) < y))"
val lem15 = hof"!x!y (-(x <= y) -> (y < x))"
val lem16 = hof"-(y <= f(x))"
val lem19 = ProofBuilder.
  c( LogicalAxiom( lem13 ) ).
  c( LogicalAxiom( lem14 ) ).
  c( LogicalAxiom( lem15 ) ).
  u( ForallElimBlock( _, List( le"y:nat", le"f(x)" ) ) ).
  c( LogicalAxiom( lem16 ) ).
  b( ImpElimRule( _, _ ) ).
  u( ExistsIntroRule( _, hof"?x (f(x) < y)" ) ).
  b( NegElimRule( _, _ ) ).
  u( BottomElimRule( _, hof"y <= f(x)" ) ).
  b( ExcludedMiddleRule( _, _ ) ).
  u( ForallIntroRule( _, hov"x:nat", hov"x:nat" ) ).
  u( ImpIntroRule( _, hof"-(?x (f(x) < y))" ) ).
  u( ForallIntroRule( _, hov"y:nat", hov"y:nat" ) ).
  qed
    */

  val lem17 = hof"(?y ((-(?x (f(x) < y))) & (?x (f(x) <= y))))"
  val lem18 = hof"(-(?x (f(x) < y))) & (?x (f(x) <= y))"
  //val lem5 = hof"!y ((-(?x f(x) < y)) -> (!x y <= f(x)))"
  val lem20 = hof"!x!y!z (x <= y & y <= z -> x <= z)"
  val coquand = ProofBuilder.
    c( LogicalAxiom( lem17 ) ).
    c( LogicalAxiom( lem18 ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem20 ) ).
    u( ForallElimBlock( _, List( le"f(x)", le"y:nat", le"f(x + a)" ) ) ).
    c( LogicalAxiom( hof"f(x) <= y" ) ).
    //c( LogicalAxiom( lem5 ) ).
    c( lem19 ).
    u( ForallElimRule( _, le"y:nat" ) ).
    c( LogicalAxiom( lem18 ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    u( ForallElimRule( _, le"x + a" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= f(x + a))" ) ).
    u( ForallIntroRule( _, hof"!a?x (f(x) <= f(x + a))", hov"a:nat" ) ).
    b( ExistsElimRule( _, _ ) ).
    u( ContractionRule( _, hof"(-(?x (f(x) < y))) & (?x (f(x) <= y))" ) ).
    b( ExistsElimRule( _, _ ) ).
    qed
  prooftool( coquand )
  val m2 = ClassicalExtraction.extractCases( coquand )
  //ScalaCodeGenerator( "coquand" )( m2 )( ClassicalExtraction.systemT( ctx ) )
  val m2Args = mutable.Map[Ty, Expr](
    List( lem13, lem14, lem15, lem17, lem18, lem20 ).zipWithIndex.map {
      case ( f, i ) => ClassicalExtraction.flat( f ) -> Const( s"arg${i + m1Args.size}", ClassicalExtraction.flat( f ) )
    }: _* )
  m2Args += realm1.ty -> realm1

  val realm2 = assignArgs( m2, m2Args )
  println( s"realm1.ty: ${realm1.ty}" )
  println( s"realm2.ty: ${realm2.ty}" )
  val Some( proj1 ) = cctx.constant( "pi1", List( ty"nat", ty"1" ) )
  //assert( normalized == normalize( normalized ) )
  var normalized = proj1( realm2( le"s(0)" ) )
  while ( normalize( normalized ) != normalized ) {
    normalized = normalize( normalized )
  }
  println( normalized )
}

object synthexManySorted extends Script {

  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.proofs.nd.InductionRule
  import gapt.proofs.reduction._
  import gapt.provers.vampire.Vampire

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'f': nat>nat>o"
  implicit var cctx = ClassicalExtraction.systemT( ctx )
  val Some( z ) = cctx.constant( "0" )
  val Some( s ) = cctx.constant( "s" )
  val Some( gt ) = cctx.constant( "gt" )
  //val Some( not ) = cctx.constant( "not" )
  val not = hoc"'not': o>o"
  cctx += PrimitiveRecursiveFunction(
    not,
    List(
      ( not( hof"true" ) -> hof"false" ),
      ( not( hof"false" ) -> hof"true" ) ) )( cctx )

  val x = hov"x:nat"
  val y = hov"y:nat"
  val plus = hoc"'+': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    plus,
    List(
      ( plus( z, y ) -> y ),
      ( plus( s( x ), y ) -> s( plus( x, y ) ) ) ) )( cctx )
  val times = hoc"'*': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    times,
    List(
      ( times( z, y ) -> z ),
      ( times( s( x ), y ) -> plus( y, times( x, y ) ) ) ) )( cctx )
  val pow2 = hoc"'pow2': nat>nat"
  cctx += PrimitiveRecursiveFunction(
    pow2,
    List(
      ( pow2( z ) -> z ),
      ( pow2( s( x ) ) -> times( s( x ), s( x ) ) ) ) )( cctx )
  val lt = hoc"'<': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    lt,
    List(
      ( lt( z, y ) -> gt( y, z ) ),
      ( lt( s( x ), y ) -> gt( y, s( x ) ) ) ) )( cctx )
  val leq = hoc"'<=': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    leq,
    List(
      ( leq( z, y ) -> not( gt( z, y ) ) ),
      ( leq( s( x ), y ) -> not( gt( s( x ), y ) ) ) ) )( cctx )
  //println( s"normalizing pow2(2): ${normalize( pow2( s( s( z ) ) ) )}" )

  val peano5 = hof"!x 0 = x*0"
  val peano7 = hof"!x!y (x<y -> s(x)<s(y))"
  val lem1 = hof"!x s(pow2(s x)) < pow2(s(s x))"
  val lem2 = hof"!x pow2(x) < pow2(s x)"
  val lem4 = hof"!x!y (y<x | x<y | x=y)"
  val lem5 = hof"!x!y!z (y<z & x<y -> x<z)"
  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val defpow2 = hof"!x x*x = pow2(x)"
  val defind = hof"!x!y ((f x y) <-> (x < pow2(s y) & pow2(y) <= x))"
  val thm1 =
    hof"""!y!x (
  s(x)<pow2(s y) & x<pow2(s y) & pow2(y)<=x ->
    s(x)<pow2(s y) & pow2(y)<=s(x)
)"""
  val ind = hof"(?y (f 0 y)) & !x ((?y (f x y)) -> (?y (f (s x) y))) -> !x?y (f x y)"
  val thm = hof"!x?y (f x y)"
  val problem = peano5 +: peano7 +: lem1 +: lem2 +: lem4 +: lem5 +: defleq +: defpow2 +: defind +: ind +: thm1 +: Sequent() :+ thm

  val tmp: ( HOLSequent, ExpansionProof => ExpansionProof ) = ErasureReductionET forward problem
  //val ind2 = tmp._1( Ant( 9 ) )
  //println( ind2 )

  import java.io._
  import gapt.formats.json._
  val f = new File( "/home/matthias/tmp/synthexManySorted.json" )
  val lk = if ( f.isFile() && f.canRead() ) {
    println( "Reading proof from JSON file..." )
    JsonImporter.load[LKProof]( f )
  } else {
    println( "Proving using Vampire..." )

    val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
    //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
    println( "Done." )
    println( "Deskolemization..." )
    val desk: ExpansionProof = expansionProof.get
    println( "Done." )
    //prooftool( desk )
    val deskInd = ExpansionProof( desk.expansionSequent.map {
      case et =>
        et.shallow match {
          case `ind` =>

            ETWeakQuantifier(
              hof"!X (X(0) ∧ ∀x (X(x) → X(s(x))) → ∀x X(x))",
              Map( le"^x ?y (f x y)" -> et ) )
          /*
case `ind2` =>
ETWeakQuantifier(
  hof"!X (X(#c(f_0:i)) ∧ ∀x_0 (X(x_0) → X(#c(f_s:i>i)(x_0))) → ∀x_0 X(x_0))", Map( le"^x_0 ?y_0 (#c(P_f:i>i>o) x_0 y_0)" -> et ) )
          */
          case _ => et
        }
    } )
    //prooftool( deskInd )

    println( "Expansion proof to LK..." )
    val lk = ExpansionProofToLK( deskInd ).getOrElse( throw new Exception( "LK proof not obtained" ) )
    println( "Done." )
    cctx.check( lk )
    val jsonLk = gapt.formats.json.JsonExporter( lk )
    val bw = new BufferedWriter( new FileWriter( f ) )
    bw.write( jsonLk.render( 80 ) )
    bw.close()
    lk
  }
  //println( "LK: num inferences: " + lk.subProofs.size )

  println( "LK to ND..." )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( "Done." )
  //println( nd )
  //prooftool( nd )
  if ( nd.subProofs.exists {
    case InductionRule( _, _, _ ) => true
    case _                        => false
  } )
    println( "contains Induction" )
  println( s"contains ${
    nd.subProofs.filter {
      case ExcludedMiddleRule( _, _, _, _ ) => true
      case _                                => false
    }.size
  } excluded middle inferences" )

  //val m1 = MRealizability.mrealize( nd, false )._2
  val m1 = ClassicalExtraction.extractCases( nd )
  println( "var map\n" + ClassicalExtraction.getVarMap.mkString( "\n" ) )
  //print( m1 ); print( " of type " ); println( m1.ty )
  //println( "free variables in m1: " + freeVariables( m1 ) )
  //println( "ND: num inferences: " + nd.subProofs.size )
  //println( "ND: num EM: " + nd.subProofs.count {
  //case _: ExcludedMiddleRule => true
  //case _                     => false
  //} )
  //FSharpCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
  val scalaProg = ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
  val scalaFile = new File( "/home/matthias/tmp/synthexManySorted.scala" )
  val bw = new BufferedWriter( new FileWriter( scalaFile ) )
  bw.write( scalaProg )
  bw.close()
  //println( "flat(thm): " + ClassicalExtraction.flat( thm ) )
  //println( "ty(m1): " + m1.ty )

  //val arg1 = le"(^(tmp:nat) i)"
  val m1Args = scala.collection.mutable.Map[Ty, Expr](
    List( peano5, peano7, lem1, lem2, lem5, defpow2, defind, thm1 ).zipWithIndex.map {
      case ( f, i ) => ClassicalExtraction.flat( f ) -> Const( s"arg$i", ClassicalExtraction.flat( f ) )
    }: _* )
  val Some( i ) = cctx.constant( "i" )

  val Some( pair ) = cctx.constant( "pair", List( ty"1>sum(1)(1)", ty"sum(1)(1)>1" ) )
  val Some( cmp ) = cctx.constant( "cmp" )
  val Some( cmp2 ) = cctx.constant( "cmp2" )

  // (y < x | x < y) | x = y)
  m1Args += ( ClassicalExtraction.flat( lem4 ) ->
    le"""
(^(tmp1:nat) (^(tmp2:nat) ($cmp tmp1 tmp2)))
""" )
  // (x<=y <-> (x=y | x<y))"
  m1Args += ( ClassicalExtraction.flat( defleq ) ->
    le"""(^(tmp3:nat) (^(tmp4:nat)
$pair(
  (^(tmp5:1) ($cmp2 tmp3 tmp4)),
  (^(tmp6:sum(1)(1)) $i)
)))""" )

  def assignArgs( prog: Expr ): Expr = prog.ty match {
    case TArr( TBase( "nat", _ ), _ ) => prog
    case TArr( argTy, _ ) =>
      val arg = m1Args( argTy )
      println( s"assigning $arg to ${prog.ty}" )
      assignArgs( prog( arg ) )
  }
  val realm1 = assignArgs( m1 )

  val Some( proj1 ) = cctx.constant( "pi1", List( ty"nat", ty"1" ) )
  /*
  println( realm1 )
  println( s"normalize\n${normalize( proj1( realm1( le"s(s(s(s(0))))" ) ) )}" )
  */
  var normalized = proj1( realm1( le"s(s(s(s(0))))" ) )

  println( "synthex program:\n" + normalized )
  //while ( normalize( normalized ) != normalized ) {
  normalized = normalize( normalized )
  //}
  println( normalized )
  /*
println( "expecting inr(i)" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"0:nat" )( le"0:nat" ) ) )
println( "expecting inl(inl(i))" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"0:nat" )( le"s(0):nat" ) ) )
println( "expecting inl(inr(i))" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"s(0):nat" )( le"0:nat" ) ) )
println( "expecting inl(i)" + normalize( m1Args( ClassicalExtraction.flat( defleq ) )( le"0:nat" )( le"0:nat" ) ) )
println( "expecting inr(i)" + normalize( m1Args( ClassicalExtraction.flat( defleq ) )( le"0:nat" )( le"s(0):nat" ) ) )
*/
}

object booleanDetVampire extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x1!x2?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( nd )
  //prooftool( nd )
  val em1SubProofs =
    nd.subProofs.filter {
      case e @ ExcludedMiddleRule( _, _, _, _) =>
        e.formulaA match {
          case Ex(_, _) => true
          case _ => false
        }
      case _                                => false
    }
  println( s"contains ${
    em1SubProofs.size
  } excluded middle inferences" )
  em1SubProofs.foreach( prooftool(_) )
  println( em1SubProofs.map( _.endSequent.succedent ) )
  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  val realm1 = m1( exception )( i )
  LogHandler.current.value = LogHandler.silent
  /*
  println( normalize( realm1( bFalse )( bFalse ) ).toUntypedString )
  println( normalize( realm1( bFalse )( bTrue ) ).toUntypedString )
  println( normalize( realm1( bTrue )( bFalse ) ).toUntypedString )
  */
  //println( realm1( bTrue )( bTrue ).toUntypedString )
  //println( normalize( realm1( bTrue )( bTrue ) ).toUntypedString )
  //println( normalize( realm1( bTrue )( bFalse ) ).toUntypedString )
  //println( normalize( realm1( bFalse )( bTrue ) ).toUntypedString )
  println( normalize( realm1( bFalse )( bFalse ) ).toUntypedString )
}

object simpleNatDet extends Script {

  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.proofs.nd.InductionRule
  import gapt.proofs.reduction._
  import gapt.provers.vampire.Vampire

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'f': nat>nat>o"
  implicit var cctx = ClassicalExtraction.systemT( ctx )
  val Some( z ) = cctx.constant( "0" )
  val Some( s ) = cctx.constant( "s" )
  val Some( gt ) = cctx.constant( "gt" )
  val Some( not ) = cctx.constant( "not" )

  val x = hov"x:nat"
  val y = hov"y:nat"
  val plus = hoc"'+': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    plus,
    List(
      ( plus( z, y ) -> y ),
      ( plus( s( x ), y ) -> s( plus( x, y ) ) ) ) )( cctx )
  val times = hoc"'*': nat>nat>nat"
  cctx += PrimitiveRecursiveFunction(
    times,
    List(
      ( times( z, y ) -> z ),
      ( times( s( x ), y ) -> plus( y, times( x, y ) ) ) ) )( cctx )
  val pow2 = hoc"'pow2': nat>nat"
  cctx += PrimitiveRecursiveFunction(
    pow2,
    List(
      ( pow2( z ) -> z ),
      ( pow2( s( x ) ) -> times( s( x ), s( x ) ) ) ) )( cctx )
  val lt = hoc"'<': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    lt,
    List(
      ( lt( z, y ) -> gt( y, z ) ),
      ( lt( s( x ), y ) -> gt( y, s( x ) ) ) ) )( cctx )
  val leq = hoc"'<=': nat>nat>o"
  cctx += PrimitiveRecursiveFunction(
    leq,
    List(
      ( leq( z, y ) -> not( gt( z, y ) ) ),
      ( leq( s( x ), y ) -> not( gt( s( x ), y ) ) ) ) )( cctx )
  //println( s"normalizing pow2(2): ${normalize( pow2( s( s( z ) ) ) )}" )

  val peano5 = hof"!x 0 = x*0"
  val peano7 = hof"!x!y (x<y -> s(x)<s(y))"
  val lem1 = hof"!x s(pow2(s x)) < pow2(s(s x))"
  val lem2 = hof"!x pow2(x) < pow2(s x)"
  val lem4 = hof"!x!y (y<x | x<y | x=y)"
  val lem5 = hof"!x!y!z (y<z & x<y -> x<z)"
  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val defpow2 = hof"!x x*x = pow2(x)"
  //val defind = hof"!x!y ((f x y) <-> (x < pow2(s y) & pow2(y) <= x))"
  val thm1 =
    hof"""!y!x (
  s(x)<pow2(s y) & x<pow2(s y) & pow2(y)<=x ->
    s(x)<pow2(s y) & pow2(y)<=s(x)
)"""
  val ind = hof"(?y (f 0 y)) & !x ((?y (f x y)) -> (?y (f (s x) y))) -> !x?y (f x y)"

  val defind = hof"!x!y ((f x y) <-> ((x = 0 & y = s(0)) | (x = s(0) & y = s(0)) | (0 < x & y = 0) | (0 < x & y = s(0))))"
  val thm = hof"!x?y (f x y)"
  val problem = defind +: ind +: peano7 +: Sequent() :+ thm

  val tmp: ( HOLSequent, ExpansionProof => ExpansionProof ) = ErasureReductionET forward problem
  //val ind2 = tmp._1( Ant( 9 ) )
  //println( ind2 )

  import java.io._
  import gapt.formats.json._
  val f = new File( "/home/matthias/tmp/simpleNatDet.json" )
  val lk = if ( f.isFile() && f.canRead() ) {
    println( "Reading proof from JSON file..." )
    JsonImporter.load[LKProof]( f )
  } else {
    println( "Proving using Vampire..." )

    val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
    //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
    println( "Done." )
    println( "Deskolemization..." )
    val desk: ExpansionProof = expansionProof.get
    println( "Done." )
    //prooftool( desk )
    val deskInd = ExpansionProof( desk.expansionSequent.map {
      case et =>
        et.shallow match {
          case `ind` =>

            ETWeakQuantifier(
              hof"!X (X(0) ∧ ∀x (X(x) → X(s(x))) → ∀x X(x))",
              Map( le"^x ?y (f x y)" -> et ) )
          /*
case `ind2` =>
ETWeakQuantifier(
  hof"!X (X(#c(f_0:i)) ∧ ∀x_0 (X(x_0) → X(#c(f_s:i>i)(x_0))) → ∀x_0 X(x_0))", Map( le"^x_0 ?y_0 (#c(P_f:i>i>o) x_0 y_0)" -> et ) )
          */
          case _ => et
        }
    } )
    //prooftool( deskInd )

    println( "Expansion proof to LK..." )
    val lk = ExpansionProofToLK( deskInd ).getOrElse( throw new Exception( "LK proof not obtained" ) )
    println( "Done." )
    cctx.check( lk )
    val jsonLk = gapt.formats.json.JsonExporter( lk )
    val bw = new BufferedWriter( new FileWriter( f ) )
    bw.write( jsonLk.render( 80 ) )
    bw.close()
    lk
  }
  //println( "LK: num inferences: " + lk.subProofs.size )

  println( "LK to ND..." )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( "Done." )
  //println( nd )
  //prooftool( nd )
  if ( nd.subProofs.exists {
    case InductionRule( _, _, _ ) => true
    case _                        => false
  } )
    println( "contains Induction" )
  println( s"contains ${
    nd.subProofs.filter {
      case ExcludedMiddleRule( _, _, _, _ ) => true
      case _                                => false
    }.size
  } excluded middle inferences" )

  //val m1 = MRealizability.mrealize( nd, false )._2
  val m1 = ClassicalExtraction.extractCases( nd )
  println( "var map\n" + ClassicalExtraction.getVarMap.mkString( "\n" ) )
  //print( m1 ); print( " of type " ); println( m1.ty )
  //println( "free variables in m1: " + freeVariables( m1 ) )
  //println( "ND: num inferences: " + nd.subProofs.size )
  //println( "ND: num EM: " + nd.subProofs.count {
  //case _: ExcludedMiddleRule => true
  //case _                     => false
  //} )
  //FSharpCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
  val scalaProg = ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
  val scalaFile = new File( "/home/matthias/tmp/synthexManySorted.scala" )
  val bw = new BufferedWriter( new FileWriter( scalaFile ) )
  bw.write( scalaProg )
  bw.close()
  //println( "flat(thm): " + ClassicalExtraction.flat( thm ) )
  //println( "ty(m1): " + m1.ty )

  //val arg1 = le"(^(tmp:nat) i)"
  val m1Args = scala.collection.mutable.Map[Ty, Expr](
    List( peano5, peano7, lem1, lem2, lem5, defpow2, defind, thm1 ).zipWithIndex.map {
      case ( f, i ) => ClassicalExtraction.flat( f ) -> Const( s"arg$i", ClassicalExtraction.flat( f ) )
    }: _* )
  val Some( i ) = cctx.constant( "i" )

  val Some( pair ) = cctx.constant( "pair", List( ty"1>sum(1)(1)", ty"sum(1)(1)>1" ) )
  val Some( cmp ) = cctx.constant( "cmp" )
  val Some( cmp2 ) = cctx.constant( "cmp2" )

  // (y < x | x < y) | x = y)
  m1Args += ( ClassicalExtraction.flat( lem4 ) ->
    le"""
(^(tmp1:nat) (^(tmp2:nat) ($cmp tmp1 tmp2)))
""" )
  // (x<=y <-> (x=y | x<y))"
  m1Args += ( ClassicalExtraction.flat( defleq ) ->
    le"""(^(tmp3:nat) (^(tmp4:nat)
$pair(
  (^(tmp5:1) ($cmp2 tmp3 tmp4)),
  (^(tmp6:sum(1)(1)) $i)
)))""" )

  def assignArgs( prog: Expr ): Expr = prog.ty match {
    case TArr( TBase( "nat", _ ), _ ) => prog
    case TArr( argTy, _ ) =>
      val arg = m1Args( argTy )
      println( s"assigning $arg to ${prog.ty}" )
      assignArgs( prog( arg ) )
  }
  val realm1 = assignArgs( m1 )

  val Some( proj1 ) = cctx.constant( "pi1", List( ty"nat", ty"1" ) )
  /*
  println( realm1 )
  println( s"normalize\n${normalize( proj1( realm1( le"s(s(s(s(0))))" ) ) )}" )
  */
  var normalized = proj1( realm1( le"s(s(s(s(0))))" ) )

  println( "synthex program:\n" + normalized )
  //while ( normalize( normalized ) != normalized ) {
  normalized = normalize( normalized )
  //}
  println( normalized )
  /*
println( "expecting inr(i)" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"0:nat" )( le"0:nat" ) ) )
println( "expecting inl(inl(i))" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"0:nat" )( le"s(0):nat" ) ) )
println( "expecting inl(inr(i))" + normalize( m1Args( ClassicalExtraction.flat( lem4 ) )( le"s(0):nat" )( le"0:nat" ) ) )
println( "expecting inl(i)" + normalize( m1Args( ClassicalExtraction.flat( defleq ) )( le"0:nat" )( le"0:nat" ) ) )
println( "expecting inr(i)" + normalize( m1Args( ClassicalExtraction.flat( defleq ) )( le"0:nat" )( le"s(0):nat" ) ) )
*/
}

object vampireZIffAAndB extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x!y?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( nd )
  //prooftool( nd )
  val em1SubProofs =
    nd.subProofs.filter {
      case e @ ExcludedMiddleRule( _, _, _, _) =>
        e.formulaA match {
          case Ex(_, _) => true
          case _ => false
        }
      case _                                => false
    }
  println( s"contains ${
    em1SubProofs.size
  } excluded middle inferences" )
  em1SubProofs.foreach( prooftool(_) )
  println( em1SubProofs.map( _.endSequent.succedent ) )
  val m1 = ClassicalExtraction.extractCases( nd )
  //val Some( i ) = ctxClassical.constant( "i" )
  val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  val realm1 = m1( exception )//( i )
  LogHandler.current.value = LogHandler.silent
  /*
  println( normalize( realm1( bFalse )( bFalse ) ).toUntypedString )
  println( normalize( realm1( bFalse )( bTrue ) ).toUntypedString )
  println( normalize( realm1( bTrue )( bFalse ) ).toUntypedString )
  */
  //println( realm1( bTrue )( bTrue ).toUntypedString )
  //println( normalize( realm1( bTrue )( bTrue ) ).toUntypedString )
  //println( normalize( realm1( bTrue )( bFalse ) ).toUntypedString )
  //println( normalize( realm1( bFalse )( bTrue ) ).toUntypedString )
  println( normalize( realm1( bFalse )( bFalse ) ).toUntypedString )
}

object vampireAIffB extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x?y ((p(x) -> p(y)) & (p(y) -> p(x)))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( nd )
  //prooftool( nd )
  val em1SubProofs =
    nd.subProofs.filter {
      case e @ ExcludedMiddleRule( _, _, _, _) =>
        e.formulaA match {
          case Ex(_, _) => true
          case _ => false
        }
      case _                                => false
    }
  println( s"contains ${
    em1SubProofs.size
  } excluded middle inferences" )
  em1SubProofs.foreach( prooftool(_) )
  println( em1SubProofs.map( _.endSequent.succedent ) )
  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  val realm1 = m1( exception )( i )
  LogHandler.current.value = LogHandler.silent
  //println( normalize( realm1( bTrue ) ).toUntypedString )
  //println( normalize( realm1( bFalse ) ).toUntypedString )

  val All(_, Ex(y, fEx)) = nd.endSequent(Suc(0))
  // Check if optimization of the ctr:r translation is possible to prevent introduction of EM1
  // as described in email on Mar 4, 2019
  def canBeOptimized(nd: NDProof, f: Formula): Boolean = {
    val containsNegPx = nd.endSequent.antecedent.exists{
      case Neg(curr) => syntacticMGU(f, curr).nonEmpty
      case _ => false
    }
    // TODO: Does it need to match with variable y?
    val containsExPx = nd.endSequent(Suc(0)) == Ex(y, f)
    if( containsNegPx && containsExPx ) {
      true
    } else {
      nd match {
        case LogicalAxiom(_) => false
        case ForallIntroRule(subProof, eigenVariable, quantifiedVariable) =>
          canBeOptimized(subProof, Substitution(quantifiedVariable, eigenVariable)(f))
        case UnaryNDProof(_, subProof) => canBeOptimized(subProof, f)
        case BinaryNDProof(_, leftSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(rightSubProof, f)
        case TernaryNDProof(_, leftSubProof, middleSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(middleSubProof, f) || canBeOptimized(rightSubProof, f)
      }
    }
  }
  println(canBeOptimized(nd, fEx))
  prooftool(lk)
}

object vampireAIffBEncodingb extends Script {

import gapt.expr._
import gapt.proofs.nd._
import gapt.proofs._
import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
import gapt.provers.vampire.Vampire

import gapt.proofs.context.Context
import gapt.proofs.nd.ClassicalExtraction
var ctx = Context.default
ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
val Some( bFalse ) = ctx.constant( "bFalse" )
val Some( bTrue ) = ctx.constant( "bTrue" )
val bIsTrue = hoc"p : bool>o"
ctx += PrimitiveRecursiveFunction(
  bIsTrue,
  List(
    ( bIsTrue( bFalse ) -> hof"false" ),
    ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
val axiom1 = hof"p(bTrue)"
val axiom2 = hof"-p(bFalse)"
//val axiom3 = hof"!x (x = bTrue | x = bFalse)"
val thmfof = hof"!x?y ((p(x) -> p(y)) & (p(y) -> p(x)))"
val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
//val problem = axiom1 +: axiom2 +: hof"p(x)" +: Sequent() :+ hof"x = bTrue"
//val problem = axiom1 +: axiom2 +: hof"x = bTrue" +: Sequent() :+ hof"p(x)"
println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
//val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
println( "Done." )
println( "Deskolemization..." )
val desk: ExpansionProof = expansionProof.get
prooftool(desk)
println(desk)
println( "Done." )
val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
prooftool(lk)
val nd = LKToND( lk, Some( Suc( 0 ) ) )
prooftool( nd )
val em1SubProofs =
  nd.subProofs.filter {
    case e @ ExcludedMiddleRule( _, _, _, _) =>
      e.formulaA match {
        case Ex(_, _) => true
        case _ => false
      }
    case _                                => false
  }
println( s"contains ${
  em1SubProofs.size
} excluded middle inferences" )
em1SubProofs.foreach( prooftool(_) )
println( em1SubProofs.map( _.endSequent.succedent ) )
val m1 = ClassicalExtraction.extractCases( nd )
val Some( i ) = ctxClassical.constant( "i" )
val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

val realm1 = m1( exception )( i )
LogHandler.current.value = LogHandler.silent
//println( normalize( realm1( bTrue ) ).toUntypedString )
//println( normalize( realm1( bFalse ) ).toUntypedString )
}

object zIffaAndb extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-(p(x) & p(y))" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"p(bTrue)" ) ).
    u(WeakeningRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom(hof"p(x) & p(y)")).
    u(WeakeningRule(_, hof"p(bTrue)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p = ProofBuilder.
    c(q2).
    c(q1).
    b(ExcludedMiddleRule(_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
}

object zIffaAndbShortCircuit extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim2Rule(_)).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p2 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(y)")).
    b(AndIntroRule(_, _)).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim1Rule(_)).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c( gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p = ProofBuilder.
    c(q1).
    c(q2).
    b(ExcludedMiddleRule(_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
}

object aIffbVampireManuallySimplified extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  val p1 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-((p(v) -> p(bTrue)) & (p(bTrue) -> p(v)))")).
    c( gapt.proofs.nd.TheoryAxiom( hof"p(bTrue)" ) ).
    u(WeakeningRule(_, hof"p(v)")).
    u(ImpIntroRule(_, Ant(0))).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(v)")).
    u(WeakeningRule(_, hof"p(bTrue)")).
    u(ImpIntroRule(_, Ant(0))).
    b(AndIntroRule(_, _)).
    b(NegElimRule(_, _)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p2 = ProofBuilder.
    c(gapt.proofs.nd.TheoryAxiom(hof"-p(bFalse)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_, _)).
    u(BottomElimRule(_, hof"p(v)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  println(p1.endSequent)
  println(p2.endSequent)
  val p = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"?y ((p(v) -> p(y)) & (p(y) -> p(v)))")).
    c(gapt.proofs.nd.LogicalAxiom(hof"(p(v) -> p(bTrue)) & (p(bTrue) -> p(v))")).
    c(gapt.proofs.nd.LogicalAxiom(hof"-(?y ((p(v) -> p(y)) & (p(y) -> p(v))))")).
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?y ((p(v) -> p(y)) & (p(y) -> p(v)))")).
    b(NegElimRule(_, _)).
    u(BottomElimRule(_, hof"(p(v) -> p(bTrue)) & (p(bTrue) -> p(v))")).
    b(ExcludedMiddleRule(_,_)).
    u(ExistsIntroRule(_, hof"?y ((p(v) -> p(y)) & (p(y) -> p(v)))")).
    b(ExcludedMiddleRule(_,_)).
    u(ForallIntroRule(_, hov"v:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
  //val resTop = normalize(lam(bTrue))
  val resBot = normalize(lam(bFalse))
  //println("normalize(lam(bTrue)):")
  //println(resTop.toUntypedString)
  println("normalize(lam(bFalse)):")
  println(resBot.toUntypedString)
}

object pairingDemonstration extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-(p(x) & p(y))" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"p(bTrue)" ) ).
    u(WeakeningRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom(hof"p(x) & p(y)")).
    u(WeakeningRule(_, hof"p(bTrue)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val lemPrf1 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    u(OrIntro1Rule(_, hof"-p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    u(OrIntro2Rule(_, hof"p(x)")).
    b(ExcludedMiddleRule(_,_)).
    qed
  val lemPrf2 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(y)")).
    b(AndIntroRule(_,_)).
    u(OrIntro1Rule(_, hof"-(p(x) & p(y))")).
    qed
  val lemPrf3 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x) & p(y)")).
    u(AndElim1Rule(_)).
    b(NegElimRule(_,_)).
    u(NegIntroRule(_, Ant(1))).
    u(OrIntro2Rule(_, hof"p(x) & p(y)")).
    qed
  val lemPrf4 = ProofBuilder.
    c(lemPrf1).
    c(lemPrf2).
    c(lemPrf3).
    t(OrElimRule(_,_,_)).
    qed
  val lemPrf5 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(y)")).
    u(OrIntro1Rule(_, hof"-p(y)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(y)")).
    u(OrIntro2Rule(_, hof"p(y)")).
    b(ExcludedMiddleRule(_,_)).
    qed
  val lemPrf6 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(y)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x) & p(y)")).
    u(AndElim2Rule(_)).
    b(NegElimRule(_,_)).
    u(NegIntroRule(_, Ant(1))).
    u(OrIntro2Rule(_, hof"p(x) & p(y)")).
    qed
  val lemPrf7 = ProofBuilder.
    c(lemPrf5).
    c(lemPrf4).
    c(lemPrf6).
    t(OrElimRule(_,_,_)).
    qed

  val p = ProofBuilder.
    c(lemPrf7).
    c(q2).
    c(q1).
    t(OrElimRule(_,_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)

  println(normalize(lam(bFalse)(bFalse)).toUntypedString)
}

object sumTypeDemonstration extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim2Rule(_)).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p2 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(y)")).
    b(AndIntroRule(_, _)).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim1Rule(_)).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c( gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val lem = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    u(OrIntro1Rule(_, hof"-p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    u(OrIntro2Rule(_, hof"p(x)")).
    b(ExcludedMiddleRule(_,_)).
    qed

  val p = ProofBuilder.
    c(lem).
    c(q1).
    c(q2).
    t(OrElimRule(_,_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
}

object vampireDNETest extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val axiom3 = hof"!x ((-(-p(x)) -> p(x)) & (p(x) -> -(-(p(x)))))"
  val thmfof = hof"!x!y?z ((-(-(p(x))) & p(y) -> p(z)) & (p(z) -> (-(-(p(x))) & p(y))))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println( nd )
  //prooftool( nd )
  val em1SubProofs =
    nd.subProofs.filter {
      case e @ ExcludedMiddleRule( _, _, _, _) =>
        e.formulaA match {
          case Ex(_, _) => true
          case _ => false
        }
      case _                                => false
    }
  println( s"contains ${ em1SubProofs.size } EM1 excluded middle inferences" )
  em1SubProofs.foreach( prooftool(_) )
  println( em1SubProofs.map( _.endSequent.succedent ) )
  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )
  prooftool(nd)
  prooftool(lk)

  val realm1 = m1( exception )( i )
  LogHandler.current.value = LogHandler.silent
  //println( normalize( realm1( bTrue ) ).toUntypedString )
  //println( normalize( realm1( bFalse ) ).toUntypedString )

  val All(_, Ex(y, fEx)) = nd.endSequent(Suc(0))
  // Check if optimization of the ctr:r translation is possible to prevent introduction of EM1
  // as described in email on Mar 4, 2019
  def canBeOptimized(nd: NDProof, f: Formula): Boolean = {
    val containsNegPx = nd.endSequent.antecedent.exists{
      case Neg(curr) => syntacticMGU(f, curr).nonEmpty
      case _ => false
    }
    // TODO: Does it need to match with variable y?
    val containsExPx = nd.endSequent(Suc(0)) == Ex(y, f)
    if( containsNegPx && containsExPx ) {
      true
    } else {
      nd match {
        case LogicalAxiom(_) => false
        case ForallIntroRule(subProof, eigenVariable, quantifiedVariable) =>
          canBeOptimized(subProof, Substitution(quantifiedVariable, eigenVariable)(f))
        case UnaryNDProof(_, subProof) => canBeOptimized(subProof, f)
        case BinaryNDProof(_, leftSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(rightSubProof, f)
        case TernaryNDProof(_, leftSubProof, middleSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(middleSubProof, f) || canBeOptimized(rightSubProof, f)
      }
    }
  }
  println(canBeOptimized(nd, fEx))
}

object vampireJiang extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x1!x2?y1?y2 ((-p(x1) & -p(x2) & -p(y1) & p(y2)) | (-p(x1) & p(x2) & -p(y1) & -p(y2)) | (-p(x1) & p(x2) & p(y1) & p(y2)) | (p(x1) & -p(x2) & -p(y1) & -p(y2)) | (p(x1) & p(x2) & p(y1) & -p(y2)))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  prooftool(nd)
  prooftool(lk)

  val All(_, All(_, Ex(y, fEx))) = nd.endSequent(Suc(0))
  // Check if optimization of the ctr:r translation is possible to prevent introduction of EM1
  // as described in email on Mar 4, 2019
  def canBeOptimized(nd: NDProof, f: Formula): Boolean = {
    val containsNegPx = nd.endSequent.antecedent.exists{
      case Neg(curr) => syntacticMGU(f, curr).nonEmpty
      case _ => false
    }
    // TODO: Does it need to match with variable y?
    val containsExPx = nd.endSequent(Suc(0)) == Ex(y, f)
    if( containsNegPx && containsExPx ) {
      true
    } else {
      nd match {
        case LogicalAxiom(_) => false
        case ForallIntroRule(subProof, eigenVariable, quantifiedVariable) =>
          canBeOptimized(subProof, Substitution(quantifiedVariable, eigenVariable)(f))
        case UnaryNDProof(_, subProof) => canBeOptimized(subProof, f)
        case BinaryNDProof(_, leftSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(rightSubProof, f)
        case TernaryNDProof(_, leftSubProof, middleSubProof, rightSubProof) =>
          canBeOptimized(leftSubProof, f) || canBeOptimized(middleSubProof, f) || canBeOptimized(rightSubProof, f)
      }
    }
  }
  println(canBeOptimized(nd, fEx))
  val em1SubProofs =
    nd.subProofs.filter {
      case e @ ExcludedMiddleRule( _, _, _, _) =>
        e.formulaA match {
          case Ex(_, _) => true
          case _ => false
        }
      case _                                => false
    }
  println( s"contains ${
    em1SubProofs.size
  } excluded middle inferences" )
  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  val realm1 = m1( exception )( i )
  LogHandler.current.value = LogHandler.silent
  //println( normalize( realm1( bTrue ) ).toUntypedString )
  //println( normalize( realm1( bFalse ) ).toUntypedString )

}

object em1Optimization extends Script {
  import gapt.expr._
  import gapt.proofs.lk.rules._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  val lkProofTmp = ProofBuilder.
    c(lk.rules.LogicalAxiom(hof"p(bTrue) & p(bTrue)")).
    u(WeakeningRightRule(_, hof"p(bTrue) & p(bTrue)")).
    u(WeakeningRightRule(_, hof"p(x1) & p(x2)")).
    u(WeakeningRightRule(_, hof"p(x1) & p(x2)")).
    qed
  val lkProof = ProofBuilder.
    c(lkProofTmp).
    u(ExistsRightRule(_, Suc(0), hof"p(x1) & p(bTrue)", le"bTrue", hov"x1: bool")).
    u(ExistsRightRule(_, Suc(0), hof"p(x1) & p(bTrue)", le"bTrue", hov"x1: bool")).
    u(ExistsRightRule(_, Suc(0), hof"p(x1) & p(x2)", le"x1: bool", hov"x1: bool")).
    u(ExistsRightRule(_, Suc(0), hof"p(x1) & p(x2)", le"x1: bool", hov"x1: bool")).
    u(ContractionRightRule(_, Suc(2), Suc(3))).
    u(ContractionRightRule(_, Suc(0), Suc(1))).
    qed
  prooftool(lkProof)
  val ndProof = LKToND(lkProof)
  prooftool(ndProof)
}

object negQuantifier extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val thmfof = hof"(-(!x p(x))) -> (?x -p(x))"
  val problem = Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  prooftool(nd)
  prooftool(lk)
}

object vampireSimpleDet extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x?y ((-p(x) & p(y)) | (p(x) & p(y)))"
  //val thmfof = hof"!x?y ((-p(x) & -p(y)) | (-p(x) & p(y)) | (p(x) & p(y)))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  prooftool(nd)
  prooftool(lk)

  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  //val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  //val realm1 = m1( i )
  val realm1 = normalize( m1( i ) )
  LogHandler.current.value = LogHandler.silent
  println("1\n" + realm1.toUntypedString)
  println("2\n" + normalize( realm1( bTrue ) ).toUntypedString )
  println("3\n" + normalize( realm1( bFalse ) ).toUntypedString )

}


object vampireQBF extends Script {

  import gapt.expr._
  import gapt.proofs.nd._
  import gapt.proofs._
  import gapt.proofs.expansion.{ ExpansionProof, ETWeakQuantifier, ExpansionProofToLK }
  import gapt.provers.vampire.Vampire

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val axiom1 = hof"p(bTrue)"
  val axiom2 = hof"-p(bFalse)"
  val thmfof = hof"!x?u!y?v!z ((-p(y) & -p(v) & -p(z)) | (p(y) & p(v) & -p(z)) | (-p(x) & -p(u) & p(z)) | (p(x) & -p(u) & p(z)) | (p(x) & p(u) & p(z)))"
  //val thmfof = hof"!x?y ((-p(x) & -p(y)) | (-p(x) & p(y)) | (p(x) & p(y)))"
  val problem = axiom1 +: axiom2 +: Sequent() :+ thmfof
  println( TptpFOLExporter.tptpProofProblem( problem ).toString() )
  val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "45m" ) ).withDeskolemization.extendToManySortedViaErasure ) getExpansionProof problem
  //val expansionProof: Option[ExpansionProof] = ( new Vampire( extraArgs = Seq( "--time_limit", "5m" ) ) ) getExpansionProof tmp._1
  println( "Done." )
  println( "Deskolemization..." )
  val desk: ExpansionProof = expansionProof.get
  println( "Done." )
  prooftool(desk)
  val lk = ExpansionProofToLK( desk ).getOrElse( throw new Exception( "LK proof not obtained" ) )
  println("lk done")
  val nd = LKToND( lk, Some( Suc( 0 ) ) )
  println("nd done")
  println(nd)
  prooftool(nd)
  prooftool(lk)

  val m1 = ClassicalExtraction.extractCases( nd )
  val Some( i ) = ctxClassical.constant( "i" )
  //val Some( exception ) = ctxClassical.constant( "exception", List( ty"1" ) )

  //val realm1 = m1( i )
  val realm1 = normalize( m1( i ) )
  LogHandler.current.value = LogHandler.silent
  println("1\n" + realm1.toUntypedString)

}