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

  def apply
   (n: Int) : Expr = Numeral(n, Zero)



  /**
   * Numeral of the form n + k where n is a series of Succ / Pred applications and k is a variable or constant
   * @param n the numeral to add to k
   * @param k the numeral expression
   * @return an expression of the form Succ(...(Succ(k))) or Pred(...(Pred(k))) 
   *         with n nestings of Succ or Pred
   * 
   * TODO: move to seperate object
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
        val Some((nrec, krec)) =  unapply(num): @unchecked // TODO (Stella): What to do in this case? 
                                                           // Error message was "pattern's type Some[(Int, gapt.expr.Expr)] is more specialized 
                                                           //                    than the right hand side expression's type Option[(Int, gapt.expr.Expr)]"
                                                           // I added this "fix", but I'm not sure if this is the right way to handle this.
        Some((nrec+1, krec))
      case Pred(num)  =>
        val Some((nrec, krec)) = unapply(num): @unchecked // Same here 
        Some((nrec - 1, krec))
      case expr => Some((0, expr))
  }



  def eq(a: Expr, b:Expr) = (a,b) match {
    case (Numeral(n, k), Numeral(m, l)) => n == m && k == l
    case _ => a == b //TODO: decide if we really want this (as a consequence f(Succ(Pred(Zero))) != f(Zero) but Succ(Pred(Zero)) == Zero)
  }


  /**
    * Check equality of two numerals modulo normalization (??)
    * TODO: So far Succ(x) != Succ(y). Is this really what we want? 
    *       Works for ground terms as expected.
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

 /**
  * Implements Definition 3.1.4 from the book
  * 
   * TODO: Maybe use a mapping of parameter/assignment pairs as an argument.
   */
object ParameterAssignment {

  def apply(e : Expr, assignment : Expr) : Expr = {
    Evaluate(apply1(e, assignment)) // TODO: In the def 3.1.4 a parameter assignment returns a numeral. 
                                    // Hence, only Succ and Zero. 
                                    // Thats why we evaluate here. 
                                    // Do we want that?
  }

  def apply1(e : Expr, assignment : Expr) : Expr = e match {
    case Zero => Zero
    case Succ(num) => Succ(apply(num,  assignment))
    case Pred(num) => Pred(apply(num,  assignment))
    case e if e.ty == Tw => assignment
    case _ => throw new IllegalArgumentException("No param!") // TODO: rethink
   

  }

}
