package at.logic.transformations.ceres

import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof
import at.logic.transformations.ceres.projections.Projections
import at.logic.calculi.resolution.base.FClause
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.algorithms.lk.CloneLKProof
import at.logic.language.hol._
import at.logic.calculi.lk.propositionalRules.Axiom
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.transformations.ceres.ACNF.SubstituteProof
import at.logic.language.lambda.typedLambdaCalculus.{App, LambdaExpression, Var}
import at.logic.language.lambda.types.{TA, ->, Ti, To}
import at.logic.language.lambda.symbols.VariableSymbolA
import at.logic.language.lambda.types.Ti
import scala.Some
import at.logic.language.lambda.types.->
import at.logic.language.lambda.types.To

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/10/13
 * Time: 7:11 PM
 * To change this template use File | Settings | File Templates.
 */
object CERES {
  val holordering = new Ordering[HOLExpression] {
    override def compare(x:HOLExpression, y:HOLExpression) : Int =  (x,y) match {
      case (x,y) if x syntaxEquals y => 0
      case (HOLVar(s1,t1), HOLVar(s2,t2) ) =>
        s1.toString() compare s2.toString() match {
          case 0 => typeordering.compare(t1,t2)
          case x => x
        }

      case (HOLConst(s1,t1), HOLConst(s2,t2) ) =>
        s1.toString() compare s2.toString() match {
          case 0 => typeordering.compare(t1,t2)
          case x => x
        }

      case (HOLApp(s1,t1), HOLApp(s2,t2)) =>
        compare(s1,s2) match {
          case 0 => compare(t1,t2)
          case x => x
        }

      case (HOLAbs(x1,t1), HOLAbs(x2,t2)) =>
        compare(x1,x2) match {
          case 0 => compare(t1,t2)
          case x => x
        }

      case (HOLVar(_,_), _            )   => -1

      case (HOLConst(_,_), HOLVar(_,_)) => 1
      case (HOLConst(_,_), _          ) => -1

      case (HOLApp(_,_), HOLVar(_,_)) => 1
      case (HOLApp(_,_), HOLConst(_,_)) => 1
      case (HOLApp(_,_), _          ) => -1

      case (HOLAbs(_,_), HOLVar(_,_))   => 1
      case (HOLAbs(_,_), HOLConst(_,_)) => 1
      case (HOLAbs(_,_), HOLApp(_,_))   => 1
      case (HOLAbs(_,_), _          )   => -1

      case _ => throw new Exception("Unhandled comparision of hol epxressions: "+x+" ? "+y)
    }
  }

  val typeordering = new Ordering[TA] {
    override def compare(x :TA,y:TA) : Int = (x,y) match {
      case (x,y) if x == y => 0
      case (t1->t2, t3 -> t4) =>
        val r = compare(t1,t3)
        if (r == 0) compare(t2,t4) else r
      case (_, _ -> _) => -1
      case (_ -> _, _) => 1
      case (To(),Ti()) => -1
      case (Ti(),To()) => 1
      case _ => throw new Exception("Unhandled case in type comparison: "+x+" ? "+y)
    }
  }

  def apply(lkproof : LKProof, refutation: RobinsonResolutionProof) = {
    //calculate projections
    val projections :Set[LKProof] = Projections(lkproof)

    //get end-sequent
    val root = lkproof.root.toFSequent
    val sorted_root = FSequent(root.antecedent.sorted(holordering), root.succedent.sorted(holordering))

    //define function to plug in a projection
    def createAxiom(fc:FClause) : LKProof = {
      fc match {
        case FClause(Nil, Atom(sym,List(x,y)) :: Nil ) if sym.toString== "=" && x == y =>
          Axiom(fc.neg, fc.pos)
        case _ =>
          val proj_es = fc.toFSequent compose root
          val fsp = FSequent(proj_es.antecedent.sorted(holordering), proj_es.succedent.sorted(holordering))
          println("Trying: "+fsp)
          projections.flatMap(
            x => {
              val r = x.root.toFSequent
              val sx = FSequent(r.antecedent.sorted(holordering), r.succedent.sorted(holordering));

              NaiveIncompleteMatchingAlgorithm.holMatch(sx.toFormula(),fsp.toFormula() )(Nil) match {
                case Some(sub) =>
                  //FSequent(fsp.antecedent.map(sub).asInstanceOf[Seq[HOLFormula]],
                  //         fsp.succedent.map(sub).asInstanceOf[Seq[HOLFormula]]) :: Nil
                  SubstituteProof(x, sub)::Nil
                case _ => Nil
              }
            }
            ).toList match {
            case Nil =>
              throw new Exception("Could not find projection of es "+root+" to "+fc+"!")
            case p::_ =>
              CloneLKProof(p)
          }
      }

      }


    //call robinson to lk
    RobinsonToLK(refutation, root, x => createAxiom(x))
  }

}
