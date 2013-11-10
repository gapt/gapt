package at.logic.transformations.ceres

import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof
import at.logic.transformations.ceres.projections.Projections
import at.logic.calculi.resolution.base.FClause
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.algorithms.lk.CloneLKProof
import at.logic.language.hol.{HOLExpression, HOLFormula, Atom, Equation}
import at.logic.calculi.lk.propositionalRules.Axiom
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.transformations.ceres.ACNF.SubstituteProof

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 11/10/13
 * Time: 7:11 PM
 * To change this template use File | Settings | File Templates.
 */
object CERES {
  val holordering = new Ordering[HOLExpression] {
    override def compare(x:HOLExpression, y:HOLExpression) =  {
      if (x.toString < y.toString) -1 else
        if (x.toString == y.toString) 0 else
        1
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
        //TODO: this is not enough, need to define a better ordering
          val fsp = FSequent(proj_es.antecedent.sorted(holordering), proj_es.succedent.sorted(holordering))

          projections.flatMap(
            x =>
              NaiveIncompleteMatchingAlgorithm.holMatch(root.toFormula(),fsp.toFormula() )(Nil) match {
                case Some(sub) =>

                  //FSequent(fsp.antecedent.map(sub).asInstanceOf[Seq[HOLFormula]],
                  //         fsp.succedent.map(sub).asInstanceOf[Seq[HOLFormula]]) :: Nil
                  SubstituteProof(x, sub)::Nil
                case _ => Nil
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
