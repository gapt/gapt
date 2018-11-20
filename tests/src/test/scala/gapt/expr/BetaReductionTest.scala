/*
 * BetaReductionTest.scala
 *
 */

package gapt.expr

import org.specs2.mutable._

class BetaReductionTest extends Specification {

  val v = Var( "v", Ti );
  val x = Var( "x", Ti );
  val y = Var( "y", Ti );
  val f = Var( "f", Ti ->: Ti );
  val g = Var( "g", Ti ->: Ti )
  val f2 = Var( "f2", Ti ->: Ti );
  val g2 = Var( "g2", Ti ->: Ti )

  "BetaReduction" should {
    "normalize correctly with outermost strategy" in {
      "- 1" in {
        val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
        val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
        val e = App( el, er )
        normalize( e ) must_== App( f, App( f, y ) )
      }
      "- 2" in {
        val e = App( App( Abs( g, Abs( y, App( g, y ) ) ), f ), v )
        normalize( e ) must_== App( f, v )
      }
      "- 3" in {
        val e = App( App( App( Abs( g2, Abs( g, Abs( y, App( g2, App( g, y ) ) ) ) ), f2 ), f ), v )
        normalize( e ) must_== App( f2, App( f, v ) )
      }
    }
    "normalize correctly with innermost strategy" in {
      val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
      val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
      val e = App( el, er )
      normalize( e ) must_== App( f, App( f, y ) )
    }
    "normalize correctly with implicit standard strategy" in {
      val er = App( Abs( v, App( Abs( x, App( f, x ) ), v ) ), y )
      val el = Abs( v, App( Abs( x, App( f, x ) ), v ) )
      val e = App( el, er )
      normalize( e ) must_== App( f, App( f, y ) )
    }
    "normalize correctly with Abs terms built from variables obtained by the Abs extractor" in {
      val x = Var( "x", Ti )
      val y = Var( "", Ti )
      val p = Var( "p", Ti ->: To )
      val px = App( p, x )
      val py = App( p, y )
      val xpx = Abs( x, px )
      val res = xpx match {
        case Abs( v, t ) => App( Abs( v, t ), y )
      }
      normalize( res ) must_== py
    }
    "normalize correctly including a simple variable renaming" in {
      val x = Var( "x", Ti )
      val z = Var( "z", Ti )
      val f = Const( "f", Ti ->: Ti ->: Ti )
      val M = App( Abs( x :: z :: Nil, App( f, x :: z :: Nil ) ), z )
      val N = Abs( x, App( f, z :: x :: Nil ) )
      val M_normalized = normalize( M )

      M_normalized must_== N
    }
    "normalize correctly 1+2=3 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val n = Var( "n", ( Ti ->: Ti ) ->: Ti ->: Ti )

      val one = Abs( f :: x :: Nil, App( f, x ) )
      val two = Abs( f :: x :: Nil, App( f, App( f, x ) ) )
      val three = Abs( f :: x :: Nil, App( f, App( f, App( f, x ) ) ) )

      val add = Abs( m :: n :: f :: x :: Nil, App( m, f :: App( n, f :: x :: Nil ) :: Nil ) )

      val result = normalize( App( add, one :: two :: Nil ) )

      result must_== three
    }
    "normalize correctly 8+3=11 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      // a church numeral is of type (Ti->Ti)->(Ti->Ti)
      val m = Var( "m", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val n = Var( "n", ( Ti ->: Ti ) ->: Ti ->: Ti )

      val three = Abs( f :: x :: Nil, App( f, App( f, App( f, x ) ) ) )
      val eight = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) )
      val eleven = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) ) ) ) )

      val add = Abs( m :: n :: f :: x :: Nil, App( m, f :: App( n, f :: x :: Nil ) :: Nil ) )

      val result = normalize( App( add, eight :: three :: Nil ) )

      result must_== eleven
    }
    "normalize correctly 2^3=8 using Church numerals" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      val two = Abs( f :: x :: Nil, App( f, App( f, x ) ) )
      val eight = Abs( f :: x :: Nil, App( f, App( f, App( f, App( f, App( f, App( f, App( f, App( f, x ) ) ) ) ) ) ) ) )

      val y = Var( "y", Ti ->: Ti )
      val g = Var( "g", ( Ti ->: Ti ) ->: Ti ->: Ti )
      val to_power_three = Abs( g :: y :: Nil, App( g, App( g, App( g, y ) ) ) )

      val result = normalize( App( to_power_three, two ) )

      result must_== eight
    }
  }
  "issue 659" in {
    normalize( le"(^y y) y x" ) must_== le"y x"
  }
  "normalize try/catch without raise with commuting conversion left" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize(
      le"""
s((^(y1: nat>exn) tryCatch(y1,
   0,
  handle(y1(x1:nat),
    s(0)))
)(exnV))""" ) must_== le"s(0)"
  }
  "normalize try/catch with commuting conversion left" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize(
      le"""
s((^(y1: nat>exn) tryCatch(y1,
    efq(y1(0)): nat,
  handle(y1(x1:nat),
    s(0)))
)(exnV))""" ) must_== le"s(s(0))"
  }
  "normalize try/catch with commuting conversion right" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize(
      le"""
(^(exnV: nat>exn) tryCatch(exnV,
    (^z efq(exnV(z)): nat),
  handle(exnV(x1:nat),
    (^(w:nat) s(w))))
)(y1)(0)""" ) must_== le"s(0)"
  }
  "normalize nested try/catch" in {
    import gapt.formats.babel.{ Notation, Precedence }
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += Notation.Infix( "+", Precedence.plusMinus )
    ctx += hoc"'+': nat>nat>nat"

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize(
      le"""
(^(y1: nat>exn) tryCatch(y1,
    (efq(y1(0:nat)): nat > nat),
  handle(y1(x1:nat),
    (^(z:nat) s(z)))
  )((^(y0: nat>exn) tryCatch(y0,
        efq(y0(s(x1))): nat,
      handle(y0(x0:nat),
        (x0 + x1))
  ))(exnV2)
))(exnV1)""" ) must_== le"s((s(0:nat): nat) + 0: nat)"
  }
  "normalize classical pairing pi1" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    val pair =
      le"""
     (^(x: nat) ^(y: nat)
       (^(f: nat>nat>exn)
         (f x y)
       )
     )"""
    val pi1 =
      le"""
     (^(p: (nat>nat>exn)>exn)
       (^(y:nat>exn) tryCatch(y,
          efq(p(^(x:nat) efq(y(x)))
        ),
        handle(y(x:nat), x)
       )
     )(exnV))
    """
    val classicalPairing = pi1( pair( hoc"0:nat", le"s(0):nat" ) )
    normalize( classicalPairing ) must_== le"0: nat"
  }
  "normalize classical pairing pi2" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit val ctxClassical = ClassicalExtraction.systemT( ctx )
    val pair =
      le"""
     (^(x: nat) ^(y: nat)
       (^(f: nat>nat>exn)
         (f x y)
       )
     )"""
    val pi2 =
      le"""
     (^(p: (nat>nat>exn)>exn)
       (^(y:nat>exn) tryCatch(y,
          efq(p(^(x:nat) y)
        ),
        handle(y(x:nat), x)
       )
     )(exnV))
    """
    val classicalPairing = pi2( pair( hoc"0:nat", le"s(0):nat" ) )
    normalize( classicalPairing ) must_== le"s(0): nat"
  }
  "commute efq(tryCatch M handle N) -> tryCatch (efq M) handle (efq N) -> (efq M)" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

    normalize( le"efq((^y0 tryCatch(y0, (M0: exn), handle(y0(x0), (N0: exn))))(exnVar)):?a" ) must_== le"efq(M0: exn): ?a"
  }
  "raise/handle without and with additional CC" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

    normalize( le"""
    efq(
      (^(y0: nat>exn) tryCatch(y0,
                        y0(0),
                        handle((y0: nat>exn)(x0:nat), (N0: nat>exn)(x0))
                      ))(exnV)): nat""" ) must_== le"efq(N0(0)): nat"
    normalize( le"""
    efq(f(
      (^(y0: nat>exn) tryCatch(y0,
                        y0(0),
                        handle((y0: nat>exn)(x0:nat), (N0: nat>exn)(x0))
                      ))(exnV))): nat""" ) must_== le"efq(f(y0(0):exn)): nat"
  }
  "handle/raise reduction" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

    implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize(
      le"""
        (^(y0: nat>exn) tryCatch(y0,
            (^(y1: nat>exn) tryCatch(y1,
                efq(y0(0)):nat,
            handle(
              (y1: nat>exn)(x0: nat), (N1: nat>nat)(x0))
            ))(exnV2),
        handle(
          (y0: nat>exn)(x0:nat), (N0: nat>nat)(x0))
        ))(exnV1): nat""" ) must_== le"N0(0):nat"
    normalize(
      le"""
        (^(y0: nat>exn) tryCatch(y0,
            (^(y1: nat>exn) tryCatch(y1,
                efq(y1(0)):nat,
            handle(
              (y1: nat>exn)(x0: nat), (N1: nat>nat)(x0))
            ))(exnV2),
        handle(
          (y0: nat>exn)(x0:nat), (N0: nat>nat)(x0))
        ))(exnV1): nat""" ) must_== le"N1(0):nat"
  }
  "reduce natRec, existsElim, tryCatch (previously problems with var substitution)" in {
    import gapt.proofs.Context
    import gapt.proofs.nd.ClassicalExtraction
    var ctx = Context.default
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
    normalize( le"""
       natRec(
         base: conj(nat)(1),
         (^(r:nat)(^(p:conj(nat)(1))
         existsElim(
           pair(r, i:1),
           (^(v1: nat) (^(v2: 1)
             (^(vLambda_13: (conj(nat)(1))>exn) tryCatch(vLambda_13,
                 (efq(vLambda_13(pair(v1, v2))):conj(nat)(1)),
                 handle(
                   (vLambda_13: (conj(nat)(1))>exn)(x: conj(nat)(1)), x
                 )
             ))(exnV)
           ) )
         ))),
         s(0))
    """ ) must_== le"pair(0, i)"
  }
}
