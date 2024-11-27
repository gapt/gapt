package gapt.expr.schema

import gapt.expr.subst.{Substitutable, Substitution}
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



object Parameter {
    /**
   * Param of the form n + k where n is a series of Succ / Pred applications and k is a variable or constant
   * @param n the numeral to add to k
   * @param k the numeral expression
   * @return an expression of the form Succ(...(Succ(k))) or Pred(...(Pred(k))) 
   *         with n nestings of Succ or Pred
   */
  def apply(n : Int, k : Expr): Expr = n match {
    case 0 => k
    case n if n > 0 => apply(n-1, Succ(k) )
    case n if n < 0 => apply(n+1, Pred(k) )
   // case _ => throw new IllegalArgumentException(s"Negative number s{n} does not have a numeral associated!")
  }


  def unapply(e : Expr): Option[(Int, Expr)] =
    e match {
     // case Zero => Some((0, Zero)) // subsumed by default case
      case Succ(num) =>
        unapply(num).map { case (nrec, krec) =>   (nrec+1, krec)  }
      case Pred(num)  =>
        unapply(num).map { case (nrec, krec) =>   (nrec-1, krec)  }
      case expr => Some((0, expr))
  }

  def eq(a: Expr, b:Expr) = (a,b) match {
    case (Parameter(n, k), Parameter(m, l)) => n == m && k == l
    case _ => a == b //TODO: decide if we really want this (as a consequence f(Succ(Pred(Zero))) != f(Zero) but Succ(Pred(Zero)) == Zero)
  }

}


object Numeral {

  def apply(n: Int) : Expr = n match {
    case 0 => Zero
    case n if n > 0 => Succ(apply(n-1))
    case n if n < 0 => Pred(apply(n+1))
  }


  def unapply(e : Expr) : Int = e match {
    case Zero => 0
    case Succ(num) => unapply(num) +1
    case Pred(num) => unapply(num) -1
  }

  /**
    * Check equality of two numerals modulo normalization (??)
    *
    * @param a Numeral expression
    * @param b Numeral expression
    * @return true, if a and b normalize to the same numeral
    */
  def eq_norm(a: Expr, b: Expr): Boolean = {
      (a, b) match {
        case (Zero | Pred(_) | Succ(_), Zero | Pred(_) | Succ(_)) => Evaluate(a) == Evaluate(b)
        case (_,_) => false
      }
    }

}


/**
  * Remove later.
  */
object Debug {
  def apply(e : Expr) : Expr = {
    println(e)
    e
  }
}


/**
  * Takes a basic term and returns a numeral containing only Zero and Succ
  * Takes an expression like Pred(Succ(Zero)) and returns Zero.
  * 
  * TODO: In case of a paramter, this method currently returns the parameter itself. 
  *       In the book this method is defined only for ground terms.
  *       Decide if we want that.
  */
object Evaluate {
  def apply(e: Expr): Expr = {
    apply1(e) match {
      case ne if ne != e => apply(ne)
      case _ => e
    }
  }

  def apply1(e : Expr) : Expr = e match {
    case Pred(Zero) => Zero
    case Pred(Succ(num)) => apply1(num)
    case Succ(Pred(num)) => apply1(num)
    case Pred(pre @ Pred(_)) => Pred(apply1(pre))
    case Succ(succ @ Succ(_)) => Succ(apply1(succ))
    case e if e.ty == Tw => e
    case _ =>  throw new IllegalArgumentException("Argument must be of type ω!")
  }
}

class ParameterAssignment(map: Map[Var, Expr]) extends Substitution(map, Map()) {
  //TODO: we inherit the general apply[T,U] version but we can not override it because of the normalization step
  // for U Var / Const the result doesn't need to be normalized. But e.g. App / Abs cases do not get normalized.
  // This probably rarely happens but should be dealt with properly.
  def apply[T](x: T)(implicit ev: Substitutable[ParameterAssignment, T, Expr]): Expr =
    Evaluate(ev.applySubstitution(this, x))

  // Special-cased for performance
  override def apply(v: Var): Expr = super.apply(v)
}
 /**
  * Implements Definition 3.1.4 from the book
  * 
   * TODO: Maybe use a mapping of parameter/assignment pairs as an argument.
   */
object ParameterAssignment {
   def apply(subs: Iterable[(Var, Expr)]): ParameterAssignment = new ParameterAssignment(Map() ++ subs)
   def apply(subs: (Var, Expr)*): ParameterAssignment = new ParameterAssignment(Map() ++ subs)
   def apply(variable: Var, expression: Expr): ParameterAssignment = new ParameterAssignment(Map(variable -> expression))
   def apply(map: Map[Var, Expr]): ParameterAssignment = new ParameterAssignment(map)
   def apply() = new ParameterAssignment(Map())

}
