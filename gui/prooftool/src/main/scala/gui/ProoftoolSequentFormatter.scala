package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/3/11
 * Time: 4:25 PM
 */

import at.logic.language.lambda.typedLambdaCalculus.{Abs, Var, App, LambdaExpression}
import at.logic.language.lambda.types.{To, ->, Ti}
import at.logic.calculi.lk.base.{SequentOccurrence, Sequent}

object ProoftoolSequentFormatter {
  //formats a lambda term to a readable string, distinguishing function and logical symbols
  def formulaToString(f:LambdaExpression) : String = f match {
    case App(x,y) => x match {
      case App(Var(name,tp),z) =>
        if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
/*    this code does not produce nice output for prime proof
      tp match {
        case ->(Ti(),->(Ti(),To())) =>
          if (name.toString.contains("<") || name.toString.contains("=") || name.toString.contains(">"))
            "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
          else name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
        case ->(To(),->(To(),To())) => "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
        case _ =>
          if (name.toString.contains("+") || name.toString.contains("*"))
            "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
          else name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
      } */
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