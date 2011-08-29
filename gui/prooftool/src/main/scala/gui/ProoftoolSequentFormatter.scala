package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.calculi.lk.base.{SequentOccurrence, Sequent}
import at.logic.language.lambda.types.{To, ->, Ti}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.schema._
import at.logic.language.fol._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._

object ProoftoolSequentFormatter {
 //formats a lambda term to a readable string, distinguishing function and logical symbols
  def formulaToString(f:LambdaExpression) : String = f match {

    // pretty print schemata
    case BigAnd(v, formula, init, end) => 
      "⋀" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"
    case BigOr(v, formula, init, end) => 
      "⋁" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"
    case t : IntegerTerm  => parseIntegerTerm(t, 0)

    case App(x,y) => x match {
      case App(Var(name,tp),z) =>
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
      case Var(name,tp) => tp match {
        case ->(To(), To()) => name.toString+formulaToString(y)
        case _ => y match {
          case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
          case _ => name.toString()+"("+formulaToString(y)+")"
        }
      }
      case _ => formulaToString(x) +"("+ formulaToString(y) +")"
    }
    case Var(name,t) => name.toString()
    case Abs(x,y) => formulaToString(y)
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
    // FIXME: in the first case, we implicitely assume
    // that all IntConsts are 0!
    // this is just done for convenience, and should be changed ASAP
    case z : IntConst => n.toString
    case v : IntVar => if (n > 0)
        v.toStringSimple + "+" + n.toString
      else
        v.toStringSimple
    case Succ(t) => parseIntegerTerm( t, n + 1 )
  }

 /*
  def formulaToString(f:SchemaExpression) : String = f match {
    case AppN(BigAndC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(BigOrC, SchemaAbs(i, formula)::lower::upper::Nil) => BigAndC.name + "<sub>" + formulaToString(i) + " = " + formulaToString(lower) + "</sub>" +
      "<sup>" + formulaToString(upper) + "</sup>" + formulaToString(formula)
    case AppN(pred, indexTerms) => formulaToString(pred)+"<sub>"+indexTerms.map( x => formulaToString(x)).mkString+"</sub>"
  }*/

  // formats a sequent to a readable string
  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f))
    }
    sb.toString
  }

  def sequentOccurenceToString(s: SequentOccurrence) : String = sequentToString(s.getSequent)
}
