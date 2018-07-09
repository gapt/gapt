package gapt.examples.church_numerals

import gapt.expr._

import scala.annotation.tailrec

/**
 * A  straightforward implementation of Church numerals. Numbers up to 50000 should work fine,
 * above various functions (beta-reduction, substitution, printing, ...) run out of stack.
 */
object num {
  @tailrec
  def alpha( x: Var, a: Expr, n: Int, acc: Expr => Expr ): Expr = n match {
    case 0          => acc( x );
    case n if n > 0 => alpha( x, a, n - 1, e => App( a, acc( e ) ) )
    case _          => throw new Exception( "Only positive church numerals allowed!" )
  }

  def apply( n: Int ) = {
    val x = hov"(x:i)"
    val a = hov"(z:i>i)"
    Abs( a, Abs( x, alpha( x, a, n, identity ) ) )
  }
}

/**
 * Computes the int value of a Church numeral.
 */
object int_of_num {
  @tailrec
  def count_app( t: Expr, n: Int ): Int = t match {
    case App( _, t_ ) => count_app( t_, n + 1 );
    case Var( _, _ )  => n
  }

  def apply( t: Expr ): Int = try {
    t match {
      case Abs( _, Abs( _, t_ ) ) => count_app( t_, 0 )
    }
  } catch {
    case _: MatchError => throw new Exception( s"$t is no church numeral!" )
  }
}

/**
 * Checks if lambda expression is a Church numeral.
 */
object is_num {
  def apply( n: Expr ) = try {
    int_of_num( n ); true
  } catch {
    case _: Exception => false
  }
}

/**
 * Addition of Church numerals. Does not check if the input is a church numeral.
 */
object plus {
  def apply( e1: Expr, e2: Expr ) =
    BetaReduction.betaNormalize( le"^(x:i>i) ^(u:i) $e1 x ($e2 x u)" )
}

/**
 * Multiplication of Church numerals. Does not check if the input is a church numeral.
 */
object times {
  def apply( e1: Expr, e2: Expr ) =
    BetaReduction.betaNormalize( le"^u $e2 ($e1 u)" )
}

/**
 * Conditional if c = 0 then e1 else e2
 */
object cond {
  def apply( e1: Expr, e2: Expr, c: Expr ) =
    BetaReduction.betaNormalize( le"^(u:i>i) ^(x:i) $c (^(y:i) $e2 u x) ($e1 u x)" )
}
