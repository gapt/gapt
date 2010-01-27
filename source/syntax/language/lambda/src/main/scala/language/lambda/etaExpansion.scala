/*
 * etaExpansion.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import at.logic.language.lambda.symbols._
import typedLambdaCalculus._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._

// etaExpansion is applied to expressions which are in \beta normal form ONLY

package etaExpansion {
  object EtaExpand {
    def apply(term: LambdaExpression): LambdaExpression = {
      term match {
        case x:Var => x

        case App(m,n) => App(apply(m),apply(n))
        
        case AbsN1(lsVars, sub) => sub.exptype match {
            case FunctionType(_, lsArgs ) if lsVars.size < lsArgs.size => {
                val v = sub.Factory.createVar(VariableStringSymbol("x"), lsArgs.head, Some(1))
                Abs(v, LambdaFactory.createApp(sub, v))
            }
            case Ti() => AbsN(lsVars, sub)
            case To() => AbsN(lsVars, sub)
            case _ => term
            
        }
      }
    }
  }

  object EtaNormalize {
    def apply(term: LambdaExpression): LambdaExpression = {
      term match {
        case t: LambdaExpression if EtaExpand.apply(term) == t => term
        case _ => EtaNormalize.apply(term)
      }
    }
  }
}
