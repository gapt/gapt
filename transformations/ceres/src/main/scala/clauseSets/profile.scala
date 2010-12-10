package at.logic.transformations.ceres.clauseSets

import at.logic.calculi.lk.base. {SequentOccurrence, AuxiliaryFormulas, LKProof}
//import at.logic.transformations.ceres.struct._
import at.logic.calculi.occurrences. {IntOccurrence, FormulaOccurrence, FOFactory}
import at.logic.language.hol.HOLFormula
import at.logic.transformations.ceres.struct._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet._

/**
 * Created by IntelliJ IDEA.
 * User: cdunchev
 * Date: 11/22/10
 * Time: 4:03 PM
 * To change this template use File | Settings | File Templates.
 */
package profile {

import at.logic.calculi.lksk.lkskExtractors.UnaryLKskProof
import at.logic.algorithms.lk.getCutAncestors
import at.logic.calculi.lksk.base. {LabelledSequentOccurrence, LabelledFormulaOccurrence}
import at.logic.calculi.lk.lkExtractors. {BinaryLKProof, UnaryLKProof}

import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import scala.collection.immutable._
import profile. {getAllAxioms}

//import at.logic.transformations.ceres.struct._
import at.logic.language.hol._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
//trait IntSetLabeledFormulaOcc {
//    def labelMark: Set[Int]
////    def isCutAnc: Boolean
//  }




   object getListOfFOccsInStruct {
    def apply(s: Struct): List[FormulaOccurrence] = s match {
      case Plus(s1,s2) => apply(s1)++apply(s2)
      case Times(s1,s2,_) => apply(s1)++apply(s2)
      case A(fo) => fo::Nil//{ println("\n\nA(fo) = "+fo);fo::Nil}
      case Dual(sub) => apply(sub)
      case e: EmptyTimesJunction =>  List[FormulaOccurrence]()
      case e: EmptyPlusJunction =>  List[FormulaOccurrence]()
      case _ => {println("\n\nERROR in getListOfFOccsInStruct");List()}
    }
  }
/*
  object printProfile {
    def apply(p: LKProof): Unit = p match {
      case ru @ Axiom(so) => printSeqOcc(ru.root)

      //unary rules
      case ru @ NegRightRule(up, r, a, p) => { apply(up);printSeqOcc(ru.root) }
      case ru @ NegLeftRule(up, r, a, p) => {  apply(up);printSeqOcc(ru.root)}
      case ru @ OrRight1Rule(up, r, a, p) => {  apply(up); printSeqOcc(ru.root)}
      case ru @ OrRight2Rule(up, r, a, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ AndLeft1Rule(up, r, a, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ AndLeft2Rule(up, r, a, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ImpRightRule(up, r, a1, a2, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ DefinitionLeftRule(up, r, a, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ DefinitionRightRule(up, r, a, p) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ExistsLeftRule(up, r, a, p, ev) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ForallRightRule(up, r, a, p, ev) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ForallLeftRule(up, r, a, p, ev) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ExistsRightRule(up, r, a, p, ev) => { apply(up); printSeqOcc(ru.root)}
      case ru @ WeakeningLeftRule(up, r, p1) => { apply(up); printSeqOcc(ru.root)}
      case ru @ WeakeningRightRule(up, r, p1) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ContractionLeftRule(up, r, a1, a2, p1) => { apply(up); printSeqOcc(ru.root)}
      case ru @ ContractionRightRule(up, r, a1, a2, p1) => { apply(up); printSeqOcc(ru.root)}

      //binary rules
      case ru @ CutRule(up1, up2, r, a1, a2) => { apply(up1);printSeqOcc(ru.root); apply(up2)}
      case ru @ AndRightRule(up1, up2, r, a1, a2, p) => { apply(up1);printSeqOcc(ru.root); apply(up2)}
      case ru @ OrLeftRule(up1, up2, r, a1, a2, p) => { apply(up1);printSeqOcc(ru.root); apply(up2)}
      case ru @ ImpLeftRule(up1, up2, r, a1, a2, p) => { apply(up1);printSeqOcc(ru.root); apply(up2)}
      case ru @ EquationLeft1Rule(up1, up2, r, a1, a2, p) => { apply(up1); printSeqOcc(ru.root); apply(up2)}
      case ru @ EquationLeft2Rule(up1, up2, r, a1, a2, p) => { apply(up1); printSeqOcc(ru.root); apply(up2)}
      case ru @ EquationRight1Rule(up1, up2, r, a1, a2, p) => { apply(up1); printSeqOcc(ru.root); apply(up2)}
      case ru @ EquationRight2Rule(up1, up2, r, a1, a2, p) => { apply(up1); printSeqOcc(ru.root); apply(up2)}
    }
  }

  object printStruct {
    def apply(s: Struct): String = s match {
      case Plus(s1,s2) => " < "+apply(s1)+"    +    "+apply(s2)+" > "
      case Times(s1,s2,_) => "{ [ "+apply(s1)+" ]  x  [ "+apply(s2)+" ] }"
      case A(fo) => fo.formula.toStringSimple// + "    id="+fo.id.toString
      case Dual(s) => "~"+apply(s)
      case EmptyTimesJunction() =>  "ET"
      case EmptyPlusJunction() =>  "EP"
      case _ =>  "Nothing to print"
    }
  }
*/
           //gets from the axioms those formula occurrences which are ancestors of fo
  object getAncAx {
    def apply(fo: FormulaOccurrence, p: LKProof): List[FormulaOccurrence] = fo.ancestors match {
      case List() if getAllAxioms.isFOccInAxiom(fo, getAllAxioms.apply(p)) => fo::Nil
      case _ => fo.ancestors.foldLeft(List[FormulaOccurrence]())((x,y) => x:::apply(y,p))
    }
  }



  object proofProfile {

    def apply(struct: Struct, proof: LKProof) = transformStructToProfile( struct, proof )

    // apply Bruno's rewrite system
    def rewrite(struct:Struct)(implicit proof: LKProof):Struct = struct match {
      case Plus(s1,s2) => Plus(rewrite(s1),rewrite(s2))
      case Times(s1,s2,auxFOccs) => {
        applyRule(rewrite(s1), rewrite(s2), auxFOccs)
      }
      case s: A => s
      case Dual(sub) => Dual(rewrite(sub))
      case e: EmptyTimesJunction => e
      case e: EmptyPlusJunction => e
    }

    def transformStructToProfile(struct:Struct, proof: LKProof) = {
      implicit val p = proof
      clausify(normalize(rewrite(struct)))
    }

    private def transformProfiledCartesianProductToStruct(cp: List[Pair[Struct,Struct]]): Struct = cp match {
      case Pair(i,j)::Nil => Times(i, j, List[FormulaOccurrence]())
      case Pair(i,j)::rest => Plus(Times(i,j, List[FormulaOccurrence]()),transformProfiledCartesianProductToStruct(rest))
    }

    private def transformNotProfiledCartesianProductToStruct(cp: List[Struct]): Struct = cp match {
      case i::Nil => i
      case i::rest => Plus(i,transformNotProfiledCartesianProductToStruct(rest))
    }

    def isRedStruct(s: Struct, anc_OfauxFOccs: List[FormulaOccurrence]): Boolean = !(getListOfFOccsInStruct(s).intersect(anc_OfauxFOccs)).isEmpty

    private def applyRule(s1:Struct, s2:Struct, auxFOccs: List[FormulaOccurrence])(implicit proof : LKProof):Struct = {
      val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))

      if(list1.size==0 || list2.size==0)
        println("ERROR, sizes = 0")

      if(list1.size==1 && list2.size==1)
        return Times(s1,s2,auxFOccs)

      def ancOfAuxFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x ::: getAncAx(y, proof)), proof)

      val black_list1 = list1.filter(s => !isRedStruct(s, ancOfAuxFOccs))
      val red_list1 = list1.filter(s => isRedStruct(s, ancOfAuxFOccs))
      val black_list2 = list2.filter(s => !isRedStruct(s, ancOfAuxFOccs))
      val red_list2 = list2.filter(s => isRedStruct(s, ancOfAuxFOccs))

      val profiledCartesianProduct = for (i <- red_list1; j <- red_list2) yield (i,j)
      val notProfiledCartesianProduct = black_list1 ::: black_list2

      if (profiledCartesianProduct.size > 0 ) // rewrite
      {
        val str2 = transformProfiledCartesianProductToStruct(profiledCartesianProduct)
        if (notProfiledCartesianProduct.size > 0)
        {
          val str1 = transformNotProfiledCartesianProductToStruct(notProfiledCartesianProduct)
          Plus(str1, str2)
        } else {
          str2
        }
      } else {
        Times(s1, s2, auxFOccs)
      }
    }

    private def getTimesJunctions(struct: Struct):List[Struct] = struct match {
      case s: Times => s::Nil
      case s: EmptyTimesJunction => s::Nil
      case s: A => s::Nil
      case s: Dual => s::Nil
      case Plus(s1,s2) => getTimesJunctions(s1):::getTimesJunctions(s2)
    }

    private def getLiterals(struct:Struct):List[Struct] = struct match {
      case s: A => s::Nil
      case s: Dual => s::Nil
      case s: EmptyTimesJunction => Nil
      case s: EmptyPlusJunction => Nil
      case Plus(s1,s2) => getLiterals(s1):::getLiterals(s2)
      case Times(s1,s2,_) => getLiterals(s1):::getLiterals(s2)
    }
  }

  object getAllAxioms {
    def apply(p: LKProof): List[SequentOccurrence] = p match {
      case CutRule(p1, p2, _, a1, a2) => apply( p1 ) ++ apply( p2 )

      case UnaryLKProof(_,p,_,_,_) => apply( p )
      case BinaryLKProof(_, p1, p2, _, _, _, _) => apply( p1 ) ++ apply( p2 )
      case Axiom(so) => so::Nil
      // support LKsk
//      case UnaryLKskProof(_,p,_,_,_) => apply( p )
    }
//
//    def getCorrespondingFOccs(fo: FormulaOccurrence, from: List[SequentOccurrence]): FormulaOccurrence = from match {
//      case so::rest if so.antecedent.contains(fo) => { if(so.succedent.size==1) so.succedent.head else new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}}
//      case so::rest if so.succedent.contains(fo) =>  { if(so.antecedent.size==1) so.antecedent.head else new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}}
//      case so::rest => getCorrespondingFOccs(fo, rest)
//      case List() => new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}
//    }
//
//    def getAllCorrespondingFOccs(lFOcc: List[FormulaOccurrence], from: List[SequentOccurrence]): List[FormulaOccurrence] = lFOcc.map(x => getCorrespondingFOccs(x,from))
//
//    def getAllCorrFOccs(lFOcc: List[FormulaOccurrence], p: LKProof) =   getAllCorrespondingFOccs(lFOcc, apply(p))
//    ancOfAuxFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x ::: getAncAx(y)), proof)
//     !(getListOfFOccsInStruct(i).intersect(ancOfAuxFOccs)).isEmpty
    def isFOccInAxiom(fo: FormulaOccurrence, from: List[SequentOccurrence]): Boolean = from match {
      case so::rest if so.antecedent.contains(fo) || so.succedent.contains(fo) => true
      case so::rest => isFOccInAxiom(fo, rest)
      case _ => false
    }

    def printCorrespSequent(fo: FormulaOccurrence, from: List[SequentOccurrence]) = from match {
      case so::rest if so.antecedent.contains(fo) || so.succedent.contains(fo) => { so.antecedent.toList.map(x => {print(x.formula)});print("  |-  "); so.succedent.toList.map(x => {print(x.formula)})}
      case so::rest => getPartnerFOccs(fo, rest)
//      case _ => List()
    }

    def getPartnerFOccs(fo: FormulaOccurrence, from: List[SequentOccurrence]): List[FormulaOccurrence] = from match {
      case so::rest if so.antecedent.contains(fo) || so.succedent.contains(fo) => so.antecedent.toList ::: so.succedent.toList
      case so::rest => getPartnerFOccs(fo, rest)
      case _ => List()
    }

    def getAllCorrespondingFOccs(lFOcc: List[FormulaOccurrence], from: List[SequentOccurrence]): List[FormulaOccurrence] = lFOcc.map(x => getPartnerFOccs(x,from)).foldLeft(List[FormulaOccurrence]())((x,y) => x:::y)

    def getAllCorrFOccs(lFOcc: List[FormulaOccurrence], p: LKProof) =   getAllCorrespondingFOccs(lFOcc, apply(p))
  }

  object printCutAncs {
    def apply(p: LKProof) = {
      getCutAncestors( p ).foreach(fo => println(fo.formula.toStringSimple))
    }
  }
}
