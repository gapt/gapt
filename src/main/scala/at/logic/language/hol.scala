/*
 * hol.scala
 */

package at.logic.language.hol

import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.{LambdaExpression, FactoryA}
import at.logic.language.hol.HOLPosition._

import scala.collection.mutable

trait HOLExpression extends LambdaExpression {

  // Factory for App, Abs and Var
  override def factory: FactoryA = HOLFactory

  // How many toString methods does one need??
  override def toString = this match {
    case HOLVar(x, tpe) => x.toString + ":" + tpe.toString
    case HOLConst(x, tpe) => x.toString + ":" + tpe.toString
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s, a) => s + ", " + a.toString)
      else args.foldLeft("")((s, a) => s + a.toString)) + "): o"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s, a) => s + ", " + a.toString)
      else args.foldLeft("")((s, a) => s + a.toString)) + "):" + tpe.toString
    case And(x, y) => "(" + x.toString + AndSymbol + y.toString + ")"
    case Equation(x, y) => "(" + x.toString + EqSymbol + y.toString + ")"
    case Or(x, y) => "(" + x.toString + OrSymbol + y.toString + ")"
    case Imp(x, y) => "(" + x.toString + ImpSymbol + y.toString + ")"
    case Neg(x) => NegSymbol + x.toString
    case ExVar(x, f) => ExistsSymbol + x.toString + "." + f.toString
    case AllVar(x, f) => ForallSymbol + x.toString + "." + f.toString
    case HOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }

  //outer pretty printing, has no parenthesis around
  //TODO: introduce binding priorities and skip more parens
  def toPrettyString: String = this match {
    case HOLVar(x, tpe) => x.toString
    case HOLConst(x, tpe) => x.toString
    case Atom(c: HOLConst, List(left, right)) if c.sym == EqSymbol =>
      left.toPrettyString_ + " " + EqSymbol + " " + right.toPrettyString_
    case Atom(x, args) =>
      x + "(" +
        (if (args.size > 1) args.head.toPrettyString_ + args.tail.foldLeft("")((s, a) => s + ", " + a.toPrettyString_)
        else args.foldLeft("")((s, a) => s + a.toPrettyString_)) + ")"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s, a) => s + ", " + a.toPrettyString_)
      else args.foldLeft("")((s, a) => s + a.toPrettyString_)) + ")"
    case And(x, y) => x.toPrettyString_ + AndSymbol + y.toPrettyString_
    case Equation(x, y) => x.toPrettyString_ + EqSymbol + y.toPrettyString_
    case Or(x, y) => x.toPrettyString_ + OrSymbol + y.toPrettyString_
    case Imp(x, y) => x.toPrettyString_ + ImpSymbol + y.toPrettyString_
    case Neg(x) => NegSymbol + x.toPrettyString_
    case ExVar(x, f) => ExistsSymbol + x.toString + "." + f.toPrettyString_
    case AllVar(x, f) => ForallSymbol + x.toString + "." + f.toPrettyString_
    case HOLAbs(v, exp) => "λ" + v.toString + "." + exp.toString
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }

  //inner pretty printing, has parenthesis around
  def toPrettyString_ : String = this match {
    case HOLVar(x, tpe) => x.toString
    case HOLConst(x, tpe) => x.toString
    case Atom(c: HOLConst, List(left, right)) if c.sym == EqSymbol =>
      left.toPrettyString_ + " = " + right.toPrettyString_
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toPrettyString_ + args.tail.foldLeft("")((s, a) => s + ", " + a.toPrettyString_)
      else args.foldLeft("")((s, a) => s + a.toPrettyString_)) + ")"
    case Function(x, args, tpe) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s, a) => s + ", " + a.toPrettyString_)
      else args.foldLeft("")((s, a) => s + a.toPrettyString_)) + ")"
    case And(x, y) => "(" + x.toPrettyString_ + AndSymbol + y.toPrettyString_ + ")"
    case Equation(x, y) => "(" + x.toPrettyString_ + EqSymbol + y.toPrettyString_ + ")"
    case Or(x, y) => "(" + x.toPrettyString_ + OrSymbol + y.toPrettyString_ + ")"
    case Imp(x, y) => "(" + x.toPrettyString_ + ImpSymbol + y.toPrettyString_ + ")"
    case Neg(x) => NegSymbol + x.toPrettyString_
    case ExVar(x, f) => ExistsSymbol + x.toString + "." + f.toPrettyString_
    case AllVar(x, f) => ForallSymbol + x.toString + "." + f.toPrettyString_
    case HOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case HOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => throw new Exception("Unrecognized symbol.")
  }

  def arity: Int = this match {
    case HOLVar(_,_) | HOLConst(_,_) => 0
    case Neg(_) | AllVar(_,_) | ExVar(_,_) => 1
    case BinaryConnective(_,_) => 2
    case Atom(_, args) => args.length
    case Function(_, args,_) => args.length
    case HOLAbs(_,_) => 1
    case _ => throw new Exception("Unhandled HOLExpression "+this+".")
  }
  /** Retrieves this expression's subexpression at a given position.
    *
    * @param pos The position to be retrieved.
    * @return The subexpression at pos.
    */
  def apply(pos: HOLPosition): HOLExpression = get(pos) match {
    case Some(f) => f
    case None => throw new Exception("Position "+pos+" does not exist in expression "+this+".")
  }

  /** Retrieves this expression's subexpression at a given position, if there is one.
    *
    * @param pos The position to be retrieved.
    * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
    */
  def get(pos: HOLPosition): Option[HOLExpression]

  /** Tests whether this expression has a subexpression at a given position.
    *
    * @param pos The position to be tested.
    * @return Whether this(pos) is defined.
    */
  def isDefinedAt(pos: HOLPosition): Boolean = toLambdaPositionOption(this)(pos) match {
    case Some(_) => true
    case None => false
  }

  /** Finds all positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find(exp: HOLExpression): List[HOLPosition] = getPositions(this, _ == exp)



}
// Should this be here?
trait Formula extends LambdaExpression {require(exptype == To)}


trait HOLFormula extends HOLExpression with Formula

case object BottomC extends HOLConst(BottomSymbol, Type("o")) with HOLFormula
case object TopC extends HOLConst(TopSymbol, Type("o")) with HOLFormula
case object NegC extends HOLConst(NegSymbol, Type("(o -> o)"))
case object AndC extends HOLConst(AndSymbol, Type("(o -> (o -> o))"))
case object OrC extends HOLConst(OrSymbol, To -> (To -> To) )
case object ImpC extends HOLConst(ImpSymbol, Type("(o -> (o -> o))"))
private[hol] class EqC(e:TA) extends HOLConst(EqSymbol, ->(e, ->(e,"o")))
object EqC {
  private val es: mutable.Map[TA,EqC] = mutable.Map[TA,EqC]()

  def apply(e:TA) = this.synchronized { es.getOrElseUpdate(e, new EqC(e)) }
  def unapply(e:HOLExpression) = e match {
    case c:HOLConst if c.sym == EqSymbol => Some(c.exptype)
    case _ => None
  }
}

// We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
object Neg {
  def apply(sub: HOLFormula) = {
    val neg = sub.factory.createConnective(NegSymbol).asInstanceOf[HOLConst]
    HOLApp(neg, sub).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(NegC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => TopC // No way to define from which layer this TopC comes from...
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )

  }
  def apply(left: HOLFormula, right: HOLFormula) = {
    val and = left.factory.createConnective(AndSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(and, left),right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(AndC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Or {
  def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
    case Nil => BottomC // No way to define from which layer this BottomC comes from...
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }
  def apply(left: HOLFormula, right: HOLFormula) : HOLFormula = {
    val or = left.factory.createConnective(OrSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(or, left), right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(HOLApp(OrC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: HOLFormula, right: HOLFormula) = {
    val imp = left.factory.createConnective(ImpSymbol).asInstanceOf[HOLConst]
    HOLApp(HOLApp(imp, left), right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(ImpC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
  }
}

object Equation {
  def apply(left: HOLExpression, right: HOLExpression) = {
    require(left.exptype == right.exptype)
    val eq = left.factory.createConnective(EqSymbol, left.exptype).asInstanceOf[HOLConst]
    HOLApp(HOLApp(eq, left),right).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
      case HOLApp(HOLApp(EqC(_),left),right) => Some( left.asInstanceOf[HOLExpression],right.asInstanceOf[HOLExpression] )
      case _ => None
  }
}

object Function {
  def apply(head: HOLVar, args: List[HOLExpression]): HOLExpression = apply_(head, args)
  def apply(head: HOLConst, args: List[HOLExpression]): HOLExpression = apply_(head, args)

  private def apply_(head: HOLExpression, args: List[HOLExpression]): HOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(HOLApp(head, t), tl)
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp(c: HOLConst,_) if isLogicalSymbol(c) => None
    case HOLApp(HOLApp(c: HOLConst,_),_) if isLogicalSymbol(c) => None
    case HOLApp(_,_) if (expression.exptype != To) => 
      unapply_(expression) match {
        case Some(t) =>
          Some( (t._1, t._2, expression.exptype) )
        case None => None
      }

    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : Option[(HOLExpression, List[HOLExpression])] = e match {
    case v: HOLVar => Some( (v, Nil) )
    case c: HOLConst => Some( (c, Nil) )
    case HOLApp(e1, e2) => 
      unapply_(e1) match {
        case Some((x,y)) =>
          Some( (x, y :+ e2) )
        case None =>
          None
      }

    case HOLAbs(_,_) =>
      None
  }
}

// HOL formulas of the form P(t_1,...,t_n)
object Atom {
  def apply(head: HOLVar, args: List[HOLExpression]): HOLFormula = apply_(head, args).asInstanceOf[HOLFormula]
  def apply(head: HOLVar): HOLFormula = head.asInstanceOf[HOLFormula]
  def apply(head: HOLConst, args: List[HOLExpression]): HOLFormula = apply_(head, args).asInstanceOf[HOLFormula]
  def apply(head: HOLConst): HOLFormula = head.asInstanceOf[HOLFormula]

  private def apply_(head: HOLExpression, args: List[HOLExpression]): HOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(HOLApp(head, t), tl)
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp(c: HOLConst,_) if isLogicalSymbol(c) => None
    case HOLApp(HOLApp(c: HOLConst,_),_) if isLogicalSymbol(c) => None
    case HOLApp(_,_) if (expression.exptype == To) => unapply_(expression) match {
      /* the head constant must be a var or a constant, e.g. (\ x.Fx) s is not atomic, but its beta normal form
       * Fs is. */
      case p@(HOLVar(_,_), _) => Some(p)
      case p@(HOLConst(_,_), _) => Some(p)
      case _ => None
    }
    case HOLConst(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case HOLVar(_,_) if (expression.exptype == To) => Some( (expression, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: HOLExpression) : (HOLExpression, List[HOLExpression]) = e match {
    case v: HOLVar => (v, Nil)
    case c: HOLConst => (c, Nil)
    case HOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2)
    case HOLAbs(x,t) =>
      (e, Nil)
  }
}

// TODO: Is it possible to simplify the quantifiers? There are too many objects for that...
class ExQ(e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
object ExQ {
  def apply(tp: TA) = new ExQ(tp)
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (HOLConst(_, t), ExistsSymbol) => Some(t)
    case _ => None
  }
}
class AllQ(e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))
object AllQ {
  def apply(tp: TA) = new AllQ(tp)
  def unapply(v: HOLConst) = (v, v.sym) match {
    case (HOLConst(_, t), ForallSymbol) => Some(t)
    case _ => None
  }
}

private object Ex {
  def apply(sub: HOLExpression) = {
    val ex = sub.factory.createConnective(ExistsSymbol, sub.exptype).asInstanceOf[HOLConst]
    HOLApp(ex, sub).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

private object All {
  def apply(sub: HOLExpression) = {
    val all = sub.factory.createConnective(ForallSymbol, sub.exptype).asInstanceOf[HOLConst]
    HOLApp(all, sub).asInstanceOf[HOLFormula]
  }
  def unapply(expression: HOLExpression) = expression match {
    case HOLApp(AllQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object ExVar {
  def apply(variable: HOLVar, sub: HOLFormula) = Ex(HOLAbs(variable, sub))
  def unapply(expression: HOLExpression) = expression match {
    case Ex(HOLAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: HOLVar, sub: HOLFormula) = All(HOLAbs(variable, sub))
  def unapply(expression: HOLExpression) = expression match {
    case All(HOLAbs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
    case _ => None
  }
}

/** A block of existential quantifiers.
 *
 */
object ExVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply(vars: List[HOLVar], sub: HOLFormula): HOLFormula = vars match {
    case Nil => sub
    case v :: vs => ExVar(v, ExVarBlock(vs, sub))
  }

  /**
   *
   * @param expression A HOLExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply(expression: HOLExpression) = expression match {
    case f: HOLFormula =>
      val (vars, sub) = unapplyHelper(f)
      if (vars.nonEmpty) Some((vars, sub))
      else None
    case _ => None
  }

  private def unapplyHelper(f: HOLFormula): (List[HOLVar], HOLFormula) = f match {
    case ExVar(v, sub) =>
      val (subVars, subF) = unapplyHelper(sub)
      (v :: subVars, subF)
    case _ => (Nil, f)
  }
}

/** A block of universal quantifiers.
  *
  */
object AllVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply(vars: List[HOLVar], sub: HOLFormula): HOLFormula = vars match {
    case Nil => sub
    case v :: vs => AllVar(v, AllVarBlock(vs, sub))
  }

  /**
   *
   * @param expression A HOLExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply(expression: HOLExpression) = expression match {
    case f: HOLFormula =>
      val (vars, sub) = unapplyHelper(f)
      if (vars.nonEmpty) Some((vars, sub))
      else None
    case _ => None
  }

  private def unapplyHelper(f: HOLFormula): (List[HOLVar], HOLFormula) = f match {
    case AllVar(v, sub) =>
      val (subVars, subF) = unapplyHelper(sub)
      (v :: subVars, subF)
    case _ => (Nil, f)
  }
}