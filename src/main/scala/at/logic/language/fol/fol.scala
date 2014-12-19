/*
 * fol.scala
 */

package at.logic.language.fol

import at.logic.language.lambda.FactoryA
import at.logic.language.hol.{HOLExpression, HOLFormula, isLogicalSymbol, EqC => HOLEqC}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._

/**
 *The following is a note about the construction of this trait. Right now FOLExpression refers to both valid FOL terms
 * and formulas and components of such valid terms and formulas, so for example, the head symbol of an atom is also a
 * fol expression although it has a complex type.
 * @author ?
 * @version ?
 */

trait FOLExpression extends HOLExpression {
  /**
   * This function takes a FOL construction and converts it to a string version. The String version is made
   * by replacing the code construction for logic symbols by string   versions in the file language/hol/logicSymbols.scala.
   * Terms are also handled by the this function.
   *
   @param  this  The method has no parameters other then the object which is to be written as a string
   *
   @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
   *
   */
  override def toString = this match {
    case FOLVar(x) => x.toString
    case FOLConst(x) => x.toString
    case FOLLambdaConst(x, t) => x + ": " + t.toString
    case Atom(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + ")"
    case Function(x, args) => x + "(" +
      (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
      else args.foldLeft("")((s,a) => s+a.toString)) + ")"
    case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
    case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
    case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
    case Neg(x) => NegSymbol + x.toString
    case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
    case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
    case FOLAbs(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
    case FOLApp(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ => 
      val r = super.toString
      throw new Exception("toString: expression is not FOL: " + r)
    }

    override def factory : FactoryA = FOLFactory
}

trait FOLFormula extends FOLExpression with HOLFormula

trait FOLTerm extends FOLExpression { require( exptype == Ti ) }

case object TopC extends FOLLambdaConst(TopSymbol, To) with FOLFormula
case object BottomC extends FOLLambdaConst(BottomSymbol, To) with FOLFormula
case object NegC extends FOLLambdaConst(NegSymbol, To -> To )
case object AndC extends FOLLambdaConst(AndSymbol, To -> (To -> To))
case object OrC extends FOLLambdaConst(OrSymbol,   To -> (To -> To))
case object ImpC extends FOLLambdaConst(ImpSymbol, To -> (To -> To))
case object EqC extends FOLLambdaConst(EqSymbol,   Ti -> (Ti -> To))

object Equation {
  def apply(left: FOLTerm, right: FOLTerm) = {
    val eq = left.factory.createConnective(EqSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(eq, left),right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
      case FOLApp(FOLApp(EqC,left),right) => Some( left.asInstanceOf[FOLTerm],right.asInstanceOf[FOLTerm] )
      case _ => None
  }
}

// FOL atom of the form P(t_1,...,t_n)
object Atom {
  def apply(head: String, args: List[FOLTerm]): FOLFormula = {
    val tp = FunctionType(To, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLFormula]
  }
  def apply(head: String): FOLFormula = FOLLambdaConst(head, To).asInstanceOf[FOLFormula]
  def apply(head: SymbolA, args: List[FOLTerm]): FOLFormula = {
    val tp = FunctionType(To, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLFormula]
  }
  def apply(head: SymbolA): FOLFormula = FOLLambdaConst(head, To).asInstanceOf[FOLFormula]
  
  private def apply_(head: FOLExpression, args: List[FOLTerm]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLLambdaConst,_) if isLogicalSymbol(c) => None
    case FOLApp(FOLApp(c: FOLLambdaConst,_),_) if isLogicalSymbol(c) => None
    case FOLApp(_,_) if (expression.exptype == To) => Some( unapply_(expression) )
    case c: FOLLambdaConst if (c.exptype == To) => Some( (c.sym, Nil) )
    case v: FOLVar if (v.exptype == To) => Some( (v.sym, Nil) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (SymbolA, List[FOLTerm]) = e match {
    //case v: FOLVar => (v.sym, Nil)
    case c: FOLLambdaConst => (c.sym, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2.asInstanceOf[FOLTerm])
  }
}

// FOL function of the form f(t_1,...,t_n)
object Function {  

  def apply(head: String, args: List[FOLTerm]): FOLTerm = {
    val tp = FunctionType(Ti, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLTerm]
  }
  def apply(head: SymbolA, args: List[FOLTerm]): FOLTerm = {
    val tp = FunctionType(Ti, args.map(a => a.exptype)) 
    val f = FOLLambdaConst(head, tp)
    apply_(f, args).asInstanceOf[FOLTerm]
  }
  
  private def apply_(head: FOLExpression, args: List[FOLTerm]): FOLExpression = args match {
    case Nil => head
    case t :: tl => apply_(FOLApp(head, t), tl)
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp(c: FOLLambdaConst,_) if isLogicalSymbol(c) => None
    case FOLApp(FOLApp(c: FOLLambdaConst,_),_) if isLogicalSymbol(c) => None
    case FOLApp(_,_) if (expression.exptype != To) => 
      val t = unapply_(expression) 
      Some( (t._1, t._2) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_(e: FOLExpression) : (SymbolA, List[FOLTerm]) = e match {
    case c: FOLLambdaConst => (c.sym, Nil)
    case FOLApp(e1, e2) => 
      val t = unapply_(e1)
      (t._1, t._2 :+ e2.asInstanceOf[FOLTerm])
  }
}

object Neg {
  def apply(sub: FOLFormula) = {
    val neg = sub.factory.createConnective(NegSymbol).asInstanceOf[FOLExpression]
    FOLApp(neg, sub).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(NegC,sub) => Some( (sub.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(fs: List[FOLFormula]) : FOLFormula = fs match {
    case Nil => TopC
    case f::fs => fs.foldLeft(f)( (d, f) => And(d, f) )
  }
  def apply(left: FOLFormula, right: FOLFormula) = {
    val and = left.factory.createConnective(AndSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(and, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(AndC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Or {
    def apply(fs: List[FOLFormula]) : FOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
  def apply(left: FOLFormula, right: FOLFormula) = {
    val or = left.factory.createConnective(OrSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(or, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(FOLApp(OrC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: FOLFormula, right: FOLFormula) = {
    val imp = left.factory.createConnective(ImpSymbol).asInstanceOf[FOLExpression]
    FOLApp(FOLApp(imp, left), right).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
      case FOLApp(FOLApp(ImpC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
      case _ => None
  }
}

private class ExQ extends FOLLambdaConst(ExistsSymbol, ->(->(Ti, To), To) )
private object ExQ {
  def apply() = new ExQ
  def unapply(v: FOLLambdaConst) = v match {
    case vo: ExQ => Some()
    case _ => None
  }
}

private class AllQ extends FOLLambdaConst( ForallSymbol, ->(->(Ti, To), To) )
private object AllQ {
  def apply() = new AllQ
  def unapply(v: FOLLambdaConst) = v match {
    case vo: AllQ => Some()
    case _ => None
  }
}

private object Ex {
  def apply(sub: FOLExpression) = {
    val ex = sub.factory.createConnective(ExistsSymbol).asInstanceOf[FOLExpression]
    FOLApp(ex, sub).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(c: ExQ, sub) => Some( sub )
    case _ => None
  }
}

private object All {
  def apply(sub: FOLExpression) = {
    val all = sub.factory.createConnective(ForallSymbol).asInstanceOf[FOLExpression]
    FOLApp(all, sub).asInstanceOf[FOLFormula]
  }
  def unapply(expression: FOLExpression) = expression match {
    case FOLApp(c: AllQ, sub) => Some( sub )
    case _ => None
  }
}

object ExVar {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: FOLExpression) = expression match {
    case Ex(FOLAbs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: FOLExpression) = expression match {
    case All(FOLAbs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

