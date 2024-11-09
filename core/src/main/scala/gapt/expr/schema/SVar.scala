package gapt.expr.schema
import gapt.expr.Var
import gapt.expr.ty._
import gapt.expr.schema.Tw
import gapt.expr._

//class Lst
//case object N extends Lst
//class Cons(val head : Int, val tail : Lst) extends Lst
//object Cons {
//  def apply(head : Int, tail : Lst) = new Cons(head, tail)
//  def unapply(cons : Cons) = Some(cons.tail)
//}
//object Head {
//  def unapply(cons : Cons) = Some(cons.head)
//}
//
//object X {
//  val x = Cons(1, Cons(2, N))
//  print(x match { case Cons(rest) => rest; case Head(h) => h})
//}


object SVar {
  def apply_simple(name : String, no_parameters : Int) = {
    var ty : Ty = Ti
    for(_ <- 1 to no_parameters ) {
      ty = Tw ->: ty
    }
    Var(name, ty)
  }

  /**
   * Creates a new schematic variable
   * @param name the name of the variable
   * @param no_parameters the number of parameters
   * @return
   */
  def apply(name : String, no_parameters : Int) = {
    val parameters = Range(0, no_parameters).map(_ => Tw)
    Var(name, FunctionType(Ti, parameters))
  }


  /* 
  
  Question:
    - Why can't I check for type Tw in method signature?
   */
  def apply(name : String, parameters : Expr*) = {
    
    val param = parameters.map(_ => Tw)
    val svar = Var(name, FunctionType(Ti, param))

    Apps(svar, parameters)
    
  }

}


