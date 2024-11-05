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

  private def apply(n : Int, calculated_sum : Expr): Expr = n match {
    case 0 => calculated_sum
    case n if n > 0 => apply(n-1, Succ(calculated_sum))
    case _ => throw new IllegalArgumentException(s"Negative number s{n} does not have a numeral associated!")
  }


  def unapply(e : Expr) = try {
    Some(convert(e))
  } catch {
    case _ : Exception => None
  }

  def convert(e : Expr): Int = {
    e match {
      case Zero => 0
      case Succ(num) => convert(num) + 1
      case Pred(num)  =>
        val res = convert(num)
        require(res > 0, s"Can't compute predecessor of ${num} because its value ${res} <= 0 !")
        res - 1
      case _ =>
        throw new IllegalArgumentException(s"Expression ${e} is not a numeral!")
    }
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
