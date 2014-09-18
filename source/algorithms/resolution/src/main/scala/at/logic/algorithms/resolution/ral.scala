package at.logic.algorithms.resolution

import at.logic.calculi.resolution.robinson.{Resolution, RobinsonResolutionProof}
import at.logic.calculi.resolution.ral.{Cut, Sub, RalResolutionProof}
import at.logic.calculi.lksk.{LabelledFormulaOccurrence, LabelledSequent}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.resolution.Clause

/**
 * Created by marty on 9/9/14.
 */


object RobinsonToRal {
  type TranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]
  val emptyTranslationMap = Map[FormulaOccurrence, LabelledFormulaOccurrence]()

  def apply(rp : RobinsonResolutionProof) : RalResolutionProof[LabelledSequent] = apply(rp, emptyTranslationMap)._2

  def apply(rp : RobinsonResolutionProof, map : TranslationMap) : (TranslationMap, RalResolutionProof[LabelledSequent]) = {
    rp match {
      case Resolution(clause, p1, p2, aux1, aux2, sub) =>
        val (rmap1, rp1) = apply(p1, map)
        val (rmap2, rp2) = apply(p2, rmap1)
        val sub1 = Sub(rp1, sub)
        val sub2 = Sub(rp2, sub)
        val rule = Cut(sub1, sub2, List(getOccFromSuccAncestor(sub1, rmap2, aux1)),
                                   List(getOccFromAnteAncestor(sub2, rmap2, aux2)))

        (rmap2, rule)

    }
  }

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
