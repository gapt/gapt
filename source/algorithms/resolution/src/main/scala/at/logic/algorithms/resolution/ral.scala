package at.logic.algorithms.resolution

import at.logic.algorithms.fol.fol2hol
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lksk.TypeSynonyms.{EmptyLabel, Label}
import at.logic.calculi.resolution.Clause
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.ral._
import at.logic.calculi.lksk.{LabelledFormulaOccurrence, LabelledSequent}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.HOLFormula

/**
 * Created by marty on 9/9/14.
 */


object RobinsonToRal {
  type TranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]
  val emptyTranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]()

  def apply(rp : RobinsonResolutionProof) : RalResolutionProof[LabelledSequent] = apply(rp, emptyTranslationMap)._2

  def apply(rp : RobinsonResolutionProof, map : TranslationMap) : (TranslationMap, RalResolutionProof[LabelledSequent]) =
    rp match {
      case InitialClause(clause) =>
        val fc : FSequent = clause.toFClause.toFSequent
        val (rule, labels) = InitialSequent(fol2hol(fc), (fc.antecedent.toList.map(x => EmptyLabel()), fc.succedent.toList.map(x => EmptyLabel())))

        (emptyTranslationMap, rule)


      case Resolution(clause, p1, p2, aux1, aux2, sub) =>
        val (rmap1, rp1) = apply(p1, map)
        val (rmap2, rp2) = apply(p2, rmap1)
        val sub1 = Sub(rp1, sub)
        val sub2 = Sub(rp2, sub)
        val rule = Cut(sub1, sub2, List(pickFOsucc(sub(aux1.formula), sub1.root, Nil)),
                                   List(pickFOant(sub(aux2.formula), sub2.root, Nil)))

        (rmap2, rule)

      case Factor(clause, parent, List(aux1@(f1::_)), sub) if clause.antecedent.contains(f1) =>
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = Sub(rp1, sub)
        val (a::aux) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOant(x.formula, rp1.root, list)::list).reverse
        val rule = AFactorF(rp1, a, aux )
        (rmap1, rule)

      case Factor(clause, parent, List(aux1@(f1::_)), sub) if clause.succedent.contains(f1) =>
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = Sub(rp1, sub)
        val (a::aux) = aux1.foldLeft(List[LabelledFormulaOccurrence]())((list,x) => pickFOant(x.formula, rp1.root, list)::list).reverse
        val rule = AFactorT(rp1, a, aux )
        (rmap1, rule)

      case Paramodulation(clause, paraparent, parent, equation, modulant, primary, sub ) if parent.root.antecedent contains modulant =>
        val (rmap1, rp1) = apply(paraparent, map)
        val (rmap2, rp2) = apply(parent, rmap1)
        val sub1 = Sub(rp1, sub)
        val sub2 = Sub(rp2, sub)
        val rule = ParaF(rp1,rp2, pickFOsucc(equation.formula, rp1.root, List()), pickFOant(modulant.formula, rp2.root, List()), primary.formula)
        (rmap2, rule)

      case Paramodulation(clause, paraparent, parent, equation, modulant, primary, sub ) if parent.root.succedent contains modulant =>
        val (rmap1, rp1) = apply(paraparent, map)
        val (rmap2, rp2) = apply(parent, rmap1)
        val sub1 = Sub(rp1, sub)
        val sub2 = Sub(rp2, sub)
        val rule = ParaT(rp1,rp2, pickFOsucc(equation.formula, rp1.root, List()), pickFOsucc(modulant.formula, rp2.root, List()), primary.formula)
        (rmap2, rule)

      case Variant(clause, parent, sub) =>
        val (rmap1, rp1) = apply(parent, map)
        val sub1 = Sub(rp1, sub)
        (rmap1, sub1)

      //TODO: handle factor rules with two contractions


  }


  def pickFO(f:HOLFormula, list : Seq[LabelledFormulaOccurrence], exclusion_list : Seq[LabelledFormulaOccurrence]) : LabelledFormulaOccurrence =
    list.find(x => x.formula == f && ! exclusion_list.contains(x)) match {
    case None => throw new Exception("Could not find auxiliary formula "+f+" in "+list.mkString("(",",",")"))
    case Some(focc) => focc
  }

  def pickFOant(f:HOLFormula, fs : LabelledSequent, exclusion_list : Seq[LabelledFormulaOccurrence]) = pickFO(f, fs.l_antecedent, exclusion_list)
  def pickFOsucc(f:HOLFormula, fs : LabelledSequent, exclusion_list : Seq[LabelledFormulaOccurrence]) = pickFO(f, fs.l_succedent, exclusion_list)

  def updateMap(map : TranslationMap, root1 : Clause, root2 : Clause, nroot : LabelledSequent) : TranslationMap = {

    val nmap1 = root1.occurrences.foldLeft(map)( (recmap, fo) => {
      nroot.occurrences.find(x => {
        require(x.ancestors.size == 1, "Ancestors of "+x+" must be exactly 1 (Substitution)")
        val newanc = x.ancestors(0).ancestors
        val oldanc = newanc.map(y => {
          map.filterKeys(_ == y).toList match {
            case x::Nil =>
              x
            case Nil =>
              throw new Exception("Could not find old ancestor match for "+y)
            case xs =>
              throw new Exception("Ambigous ancestor mapping for "+y+": all in "+xs+" map to it!")
          }
        })

        true
      }) match {
        case None =>
          throw new Exception()
        case Some(_) =>
          throw new Exception()
      }

    })
    map

  }



  def getOccFromAnteAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence) =
    getOccFromAncestor(ralp, map, occ, false)
  def getOccFromSuccAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence) =
    getOccFromAncestor(ralp, map, occ, true)
  def getOccFromAncestor(ralp : RalResolutionProof[LabelledSequent], map : TranslationMap, occ : FormulaOccurrence, side : Boolean) = {
    val occurrences = if (side == false) ralp.root.l_antecedent else ralp.root.l_succedent
    val ancocc = occurrences.find(x => {
      x.ancestors match {
        case List(pocc) if map(occ) == pocc => true
        case _ => false
      }
    })

    ancocc match {
      case None =>
        throw new Exception("Could not find occurrence "+occ+ " in ancestors of an occurrence in "+ralp.root)
      case Some(fo) =>
        fo
    }
  }


}
