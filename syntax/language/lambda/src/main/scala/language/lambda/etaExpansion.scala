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
    var s: Set[Var] = new Set[Var]()
//    def getSet() = s
    def apply(term: LambdaExpression): LambdaExpression = {
      term match {
        case x:Var => x.exptype match {
            case Ti() => x
            case To() => x
            case FunctionType(_, lsArgs ) => {
              val binders: List[Var] = lsArgs.map(z => { val fv = freshVar(z, s, x); s=s.+(fv); fv })
              AbsN(binders, AppN(term, binders.map((z => apply(z)))))
            }
        }

        case App(m,n) => {
          term.exptype match {
            case Ti() => term
            case To() => term
            case FunctionType(to, lsArgs) => {
              val binders: List[Var] = lsArgs.map(z => { val fv = freshVar(z, s, term); s=s.+(fv); fv })
              AbsN(binders, AppN(App(m,apply(n)), binders.map((z => apply(z)))))
            }
          }
        }

        case AbsN1(lsVars, sub) => {
          AbsN(lsVars, apply(sub))
        }
      }
    }
  }

  object EtaNormalize {
    def apply(term: LambdaExpression): LambdaExpression = {
      val term2 = EtaExpand(term)
      if (term2 == term) term else EtaNormalize(EtaExpand(term))
    }
  }
}











                    /*
package etaExpansion {
  object EtaExpand {
    def apply(term: LambdaExpression): LambdaExpression = {
      term match {
        case x:Var => x

        case App(m,n) => App(apply(m),apply(n))
        
        case AbsN1(lsVars, sub) => sub.exptype match {
            case FunctionType(_, lsArgs ) if lsVars.size < lsArgs.size => {
                val v = sub.factory.createVar(VariableStringSymbol("x"), lsArgs.head, Some(1))
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
      val term2 = EtaExpand(term)
      if (term2 == term) term else EtaNormalize(EtaExpand(term))
    }
  }
}
                      */