package gapt.expr.schema

import gapt.expr.ty._
import gapt.expr.{App, Const, Expr, Var, VarOrConst}
import gapt.formats.verit.alethe.True
import gapt.formats.verit.alethe.False

object Zero extends Const("0", Tw, Nil) {
  def unapply(e:Expr) : Option[Unit] = e match {
    case Const("0", Tw, Nil) => Some(())
    case _ => None
  }
}

object Succ extends Const("s", Tw ->: Tw, Nil) {
  def unapply(e : Expr) : Option[Expr] = e match {
    case App(Const("s", Tw ->: Tw, Nil), num) => Some(num)
    case _ => None
  }
}

object Pred extends Const("p", Tw ->: Tw, Nil) {
  def unapply(e : Expr) : Option[Expr] = e match {
    case App(Const("p", Tw ->: Tw, Nil), num) => Some(num)
    case _ => None
  }
}

object Numeral {

  def apply(n: Int) : Expr = Numeral(n, Zero)

  /**
   * Numeral of the form n + k where n is a series of Succ / Pred applications and k is a variable or constant
   * @param n the numeral to add to k
   * @param k the numeral expression
   * @return an expression of the form Succ(...(Succ(k))) with n nestings of Succ
   */
  def apply(n : Int, k : Expr): Expr = n match {
    case 0 => k
    case n if n > 0 => apply(n-1, Succ(k))
    case _ => throw new IllegalArgumentException(s"Negative number s{n} does not have a numeral associated!")
  }

  def eq(a: Expr, b:Expr) = (a,b) match {
    case (Numeral(n, k), Numeral(m, l)) => n == m && k == l
    case _ => a == b //TODO: decide if we really want this (as a consequence f(Succ(Pred(Zero))) != f(Zero) but Succ(Pred(Zero)) == Zero)
  }


  def unapply(e : Expr): Option[(Int, Expr)] =
    e match {
      //case Zero => Some((0, Zero)) // subsumed by default case
      case Succ(num) =>
        val Some((nrec, krec)) =  unapply(num)
        Some((nrec+1, krec))
      case Pred(num)  =>
        val Some((nrec, krec)) = unapply(num)
        require(nrec > 0, s"Can't compute predecessor of ${num} because its value ${nrec} <= 0 !") // TODO: is this really an invariant?
        Some((nrec - 1, krec))
      case expr => Some((0, expr))
  }

  /*
  Check equality of two numerals modulo normalization (??)
  TODO:
    - How to check for equality without calling equals again. --> Avoid infinite loop!
  */
  def equalsTest(a: Expr, b: Expr): Boolean = {
      (a, b) match {
        case (Zero | Pred(_) | Succ(_), Zero | Pred(_) | Succ(_)) => Normalize(a).equals(Normalize(b))
        case (_,_) => false
      }
    }
  




  //TODO: remove at some point, superfluous
  def apply_nontailrec(n : Int): Expr = n match {
    case 0 => Zero
    case n if n > 0 => Succ(apply(n-1))
    case _ => throw new IllegalArgumentException(s"Negative number s{n} does not have a numeral associated!")
  }

}

object Debug {
  def apply(e : Expr) : Expr = {
    println(e)
    e
  }
}

object Normalize {
  def apply(e: Expr): Expr = {
    apply1(e) match {
      case ne if ne != e => apply(ne)
      case _ => e
    }
  }

  def apply1(e : Expr) : Expr = e match {
    case Pred(Succ(num)) => apply1(num)
    case Succ(Pred(num)) => apply1(num)
    case Pred(pre @ Pred(_)) => Pred(apply1(pre))
    case Succ(succ @ Succ(_)) => Succ(apply1(succ))
    case e if e.ty == Tw => e
    case _ =>  throw new IllegalArgumentException("Argument must be of type ω!")
  }
}
