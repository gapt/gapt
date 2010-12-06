package at.logic.transformations.ceres.clauseSets

import at.logic.calculi.lk.base. {SequentOccurrence, AuxiliaryFormulas, LKProof}
//import at.logic.transformations.ceres.struct._
import at.logic.calculi.occurrences. {IntOccurrence, FormulaOccurrence, FOFactory}
import at.logic.language.hol.HOLFormula
import profile._

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


//  object toLabeledProof {
//    var cnt = 0;
//    def fact = new LabeledFOFactory(cnt)
//    def apply(p: LKProof): LKProof = p match {
//      case Axiom(so) => {
//        println("\ncnt = "+cnt+"   "+so.getSequent.toString)
//        cnt = cnt+1
//        Axiom(so.getSequent)(new LabeledFOFactory(cnt))// should not cause a problem because factories are not used in binary rules
//      }
//      //unary rules
//      case NegRightRule(up, r, a, p) => NegRightRule(apply(up),a)
//      case NegLeftRule(up, r, a, p) => NegLeftRule(apply(up),a)
//      case OrRight1Rule(up, r, a, p) => {
//        val (_, newf) = Or.unapply(p.formula).get
//        OrRight1Rule(apply(up), a, newf)
//      }
//      case OrRight2Rule(up, r, a, p) => {
//        val (newf, _) = Or.unapply(p.formula).get
//        OrRight2Rule(apply(up),newf,a)
//      }
//      case AndLeft1Rule(up, r, a, p) => {
//        val (_,newf) = And.unapply(p.formula).get
//        AndLeft1Rule(apply(up),a, newf)
//      }
//      case AndLeft2Rule(up, r, a, p) => {
//        val (newf, _) = And.unapply(p.formula).get
//        AndLeft2Rule(apply(up),newf, a)
//      }
//      case ImpRightRule(up, r, a1, a2, p) => ImpRightRule(apply(up),a1,a2)
//      case DefinitionLeftRule(up, r, a, p) => DefinitionLeftRule(apply(up),a, p.formula)
//      case DefinitionRightRule(up, r, a, p) => DefinitionRightRule(apply(up),a,p.formula)
//      case ExistsLeftRule(up, r, a, p, ev) => ExistsLeftRule(apply(up), a, p.formula, ev)
//      case ForallRightRule(up, r, a, p, ev) => ForallRightRule(apply(up), a, p.formula, ev)
//      case ForallLeftRule(up, r, a, p, ev) => ForallLeftRule(apply(up), a, p.formula, ev)
//      case ExistsRightRule(up, r, a, p, ev) => ExistsRightRule(apply(up), a, p.formula, ev)
//      case WeakeningLeftRule(up, r, p1) => WeakeningLeftRule(apply(up), p1.formula)(fact)
//      case WeakeningRightRule(up, r, p1) => WeakeningRightRule(apply(up), p1.formula)(fact)
//      case ContractionLeftRule(up, r, a1, a2, p1) => ContractionLeftRule(apply(up), a1, a2)
//      case ContractionRightRule(up, r, a1, a2, p1) => ContractionRightRule(apply(up), a1, a2)
//
//      //binary rules
//      case CutRule(up1, up2, r, a1, a2) => CutRule(apply(up1), apply(up2), a1, a2)
//      case AndRightRule(up1, up2, r, a1, a2, p) => {
//        println("\nandR"+"  "+up1.toString+"    "+up2.toString  +"   "+a1.formula+"   "+a2.formula)
//        AndRightRule(apply(up1), apply(up2), a1.formula, a2.formula)
//      }
//      case OrLeftRule(up1, up2, r, a1, a2, p) => OrLeftRule(apply(up1), apply(up2), a1, a2)
//      case ImpLeftRule(up1, up2, r, a1, a2, p) => ImpLeftRule(apply(up1), apply(up2), a1, a2)
//      case EquationLeft1Rule(up1, up2, r, a1, a2, p) => EquationLeft1Rule(apply(up1), apply(up2), a1, a2, p.formula)
//      case EquationLeft2Rule(up1, up2, r, a1, a2, p) => EquationLeft2Rule(apply(up1), apply(up2), a1, a2, p.formula)
//      case EquationRight1Rule(up1, up2, r, a1, a2, p) => EquationRight1Rule(apply(up1), apply(up2), a1, a2,p.formula)
//      case EquationRight2Rule(up1, up2, r, a1, a2, p) => EquationRight2Rule(apply(up1), apply(up2), a1, a2, p.formula)
//    }
//  }

///*private[profile]*/ class LabeledFOFactory(cnt: Int) extends PointerFOFactory {
//    override def createPrincipalFormulaOccurrence(formula: HOLFormula, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence]): FormulaOccurrence = {
//      val othersCast = others.asInstanceOf[Set[IntOccurrence]]
//      val max = othersCast.foldLeft(0)((prev, fo) => scala.math.max(prev, fo.label))
//      new FormulaOccurrence(formula, ancestors) with IntOccurrence with IntSetLabeledFormulaOcc {
//        def factory = LabeledFOFactory.this;
//        def label = max+1;
//        def labelMark = if(ancestors.isEmpty) Set[Int](cnt) else ancestors.foldLeft(Set[Int]())((x,y) => x.++(y.asInstanceOf[IntSetLabeledFormulaOcc].labelMark))
//      }
//    }
//    // we check how many are before the position and then substract them if needed. binary_others is used to add as prefix the size of the set of the left upper rule
//    override def createContextFormulaOccurrence(formula: HOLFormula, current: FormulaOccurrence, ancestors: List[FormulaOccurrence], others: Set[FormulaOccurrence], binary_others: Set[FormulaOccurrence]): FormulaOccurrence = {
//      val othersCast = others.asInstanceOf[Set[IntOccurrence]]
//      val currentCast = current.asInstanceOf[IntOccurrence]
//      val pos = othersCast.filter(x => x< currentCast).size + 1
//      new FormulaOccurrence(formula, ancestors) with IntOccurrence with IntSetLabeledFormulaOcc {
//        def factory = LabeledFOFactory.this;
//        def label = pos + binary_others.size;
//        def labelMark = ancestors.foldLeft(Set[Int]())((x,y) => x.++(y.asInstanceOf[IntSetLabeledFormulaOcc].labelMark))
//      }
//    }
//  }

  object printProfile {
    def printSeqOcc(s: SequentOccurrence) = {
//      println("\n")
//      s.antecedent.map(x => {println("<"+x.formula+", "+ (x.asInstanceOf[IntSetLabeledFormulaOcc]).labelMark.toString+">, "); x} )
//      println(" |- ")
//      s.succedent.map(x => {println("<"+x.formula+", "+ (x.asInstanceOf[FormulaOccurrence with IntOccurrence with IntSetLabeledFormulaOcc]).labelMark.toString+">, "); x} )
    }

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

//  object rewriteStructToProfile {
//    def apply(s: Struct): List[FormulaOccurrence] = s match {
//      case A(fo) => fo::Nil
//      case Plus(l,r) => apply(l) ::: apply (r)
//      case Times(l,r) => {
//        val left = apply(l)
//        val right = apply(r)
//
//      }
//    }
//  }


  //set of IntLabels of the formula occ. which are in a given Struct
//  object getLabelsOfStruct {
//    def apply(s: Struct): Set[Int] = s match {
//      case Plus(s1,s2) => apply(s1)++apply(s2)
//      case Times(s1,s2) => apply(s1)++apply(s2)
//      case A(fo) => fo.asInstanceOf[FormulaOccurrence with IntOccurrence with IntSetLabeledFormulaOcc].labelMark
//      case s: Dual => Set[Int]()
//      case e: EmptyTimesJunction => Set[Int]()
//      case e: EmptyPlusJunction => Set[Int]()
//    }
//  }

   object getListOfFOccsInStruct {
    def apply(s: Struct): List[FormulaOccurrence] = s match {
      case Plus(s1,s2) => apply(s1)++apply(s2)
      case Times(s1,s2,_) => apply(s1)++apply(s2)
      case A(fo) => fo::Nil//{ println("\n\nA(fo) = "+fo);fo::Nil}
      case Dual(sub) => apply(sub)
      case e: EmptyTimesJunction =>  List[FormulaOccurrence]()
      case e: EmptyPlusJunction =>  List[FormulaOccurrence]()
      case _ => {println("\n\nERROR");List()}
    }
  }

  object printStruct {
    def apply(s: Struct): String = s match {
      case Plus(s1,s2) => "( "+apply(s1)+" + "+apply(s2)+" )"
      case Times(s1,s2,_) => "( "+apply(s1)+" x "+apply(s2)+" )"
      case A(fo) => fo.formula.toStringSimple// + "    id="+fo.id.toString
      case Dual(s) => "~"+apply(s)
      case e: EmptyTimesJunction =>  "ET"
      case e: EmptyPlusJunction =>  "EP"
    }
  }

           //gets the axioms formula occurrences which are ancestors of fo
  object getAncAx {
    def apply(fo: FormulaOccurrence): List[FormulaOccurrence] = fo.ancestors match {
      case List() => fo::Nil
      case _ => fo.ancestors.foldLeft(List[FormulaOccurrence]())((x,y) => x:::apply(y))
    }
  }


  class proofProfile(val proof: LKProof) {

//    def endSeqAuxFOccsLabels(p: LKProof): Set[Int] = {
//      Set()
//    }

//    def listOfAuxFOccsOfEndSeq = getAllAxioms.getAllCorrFOccs(proof.asInstanceOf[AuxiliaryFormulas].aux.foldLeft(List[FormulaOccurrence]())((x,y)=> x:::y).foldLeft(List[FormulaOccurrence]())((x,y) => x:::getAncAx(y)), proof)

//    def normalize(struct:Struct):Struct = struct match {
//      case Plus(s1,s2) => Plus(normalize(s1), normalize(s2))
//      case Times(s1,s2) => merge(normalize(s1), normalize(s2))
//      case s: A => s
//      case s: Dual => s
//      case e: EmptyTimesJunction => e
//      case e: EmptyPlusJunction => e
//    }


    def normalize(struct:Struct):Struct = struct match {
      case Plus(s1,s2) => Plus(normalize(s1),normalize(s2))
      case Times(s1,s2,auxFOccs) => {

        val (str1,str2) = (normalize(s1), normalize(s2))
//        println("\n\nThe struct x : ")
//        printStruct(struct)
//        println("\n\nstr1 : ")
//        printStruct(str1)
//        println("\n\nstr2 : ")
//        printStruct(str2)
        merge(str1, str2, auxFOccs)
      }
      case s: A => s
      case Dual(sub) => Dual(normalize(sub))
      case e: EmptyTimesJunction => e
      case e: EmptyPlusJunction => e
    }

    def transformStructToProfile(struct:Struct) = clausify(normalize(struct))

//    def transformStructToLabelledClauseSet(struct:Struct) =
//      transformStructToClauseSet(struct).map( so => sequentOccurrenceToLabelledSequentOccurrence( so ) )

    private def transformProfiledCartesianProductToStruct(cp: List[Pair[Struct,Struct]]): Struct = cp match {
      case Pair(i,j)::Nil => Times(i, j, List[FormulaOccurrence]())
      case Pair(i,j)::rest => Plus(Times(i,j, List[FormulaOccurrence]()),transformProfiledCartesianProductToStruct(rest))
      case Nil => EmptyPlusJunction()
    }
//      def transformNotProfiledCartesianProductToStruct(cp: List[Struct]): Struct = cp.foldLeft(EmptyPlusJunction())((x,y)=>Plus(x,y))
    private def transformNotProfiledCartesianProductToStruct(cp: List[Struct]): Struct = cp match {
      case i::Nil => i
      case i::rest => Plus(i,transformNotProfiledCartesianProductToStruct(rest))
      case Nil => EmptyPlusJunction()
    }



    private def merge(s1:Struct, s2:Struct, auxFOccs: List[FormulaOccurrence]):Struct = {
      val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))
      if(list1.size==1 && list2.size==1)
        return Times(s1,s2,auxFOccs)
//      println("\n\n\n\n\n\nlist1.head : "+ printStruct(list1.head))
//      println("\n\nlist2.head : "+ printStruct(list2.head))

//      def correspFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x:::getAncAx(y)), proof)
      def correspFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x ::: getAncAx(y)), proof)

      println("\n\n\n\n\n1\ns1 : "+ printStruct(s1))
      println("\n\ns2 : "+ printStruct(s2))

      println("\n2\n\n\nauxFOccs = "+auxFOccs.map(x => {print(", "+x.id);x.formula}).toString)

//      println("\ngetListOfFOccsInStruct(i) = "+getListOfFOccsInStruct(list1.head))

//      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getListOfFOccsInStruct(i).intersect(correspFOccs)).isEmpty && !(getListOfFOccsInStruct(j).intersect(correspFOccs)).isEmpty) yield (i,j)
      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getListOfFOccsInStruct(i).intersect(correspFOccs)).isEmpty && !(getListOfFOccsInStruct(j).intersect(correspFOccs)).isEmpty) yield (i,j)
      println("\n\nprofiledCartesianProduct = "+profiledCartesianProduct.toString + "    "+profiledCartesianProduct.size)

      val notProfiledCartesianProduct = for (i <- list1++list2; if !(profiledCartesianProduct.map(x => x._1).contains(i)) && !(profiledCartesianProduct.map(x => x._2).contains(i))) yield i
      println("\n\nnotProfiledCartesianProduct = "+notProfiledCartesianProduct.toString + "    "+notProfiledCartesianProduct.size)

//      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getLabelsOfStruct(i).intersect(endSeqAuxFOccsLabels(proof))).isEmpty && !(getLabelsOfStruct(j).intersect(endSeqAuxFOccsLabels(proof))).isEmpty) yield (i,j)
//      val notProfiledCartesianProduct = for (i <- list1++list2; if !(profiledCartesianProduct.map(x => x._1).contains(i)) && !(profiledCartesianProduct.map(x => x._2).contains(i))) yield i

      val str1 = transformNotProfiledCartesianProductToStruct(notProfiledCartesianProduct)
      val str2 = transformProfiledCartesianProductToStruct(profiledCartesianProduct)
      println("\n\nmerge = "+printStruct(str1))
      Plus(str1, str2)
    }

    private def getTimesJunctions(struct: Struct):List[Struct] = struct match {
      case s: Times => s::Nil
      case s: EmptyTimesJunction => s::Nil
      case s: A => s::Nil
      case s: Dual => s::Nil
      case s: EmptyPlusJunction => Nil
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



    private def clausifyTimesJunctions(struct: Struct): SequentOccurrence = {
      def isDual(s:Struct):Boolean = s match {case x: Dual => true; case _ => false}
      val literals = getLiterals(struct)
      val (negative,positive) = literals.partition(x => isDual(x))
      val negativeFO: List[FormulaOccurrence] = negative.map(x => x.asInstanceOf[Dual].sub.asInstanceOf[A].formula) // extracting the formula occurrences from the negative literal structs
      val positiveFO: List[FormulaOccurrence] = positive.map(x => x.asInstanceOf[A].formula)     // extracting the formula occurrences from the positive atomic struct
      def convertListToSet[T](list:List[T]):Set[T] = list match {
        case x::rest => convertListToSet(rest)+x
        case Nil => new HashSet[T]
      }
      if(negativeFO.size == 0 && positiveFO.size == 0)
      println("\nError in clausifyTimesJunctions\n")
      SequentOccurrence(negativeFO.toSet, positiveFO.toSet)
    }

    def clausify(struct: Struct): List[SequentOccurrence] = {
      val timesJunctions = getTimesJunctions(struct)
      timesJunctions.map(x => clausifyTimesJunctions(x))
    }
  }

  object removeTautologies {
    def apply(l: List[Sequent]): List[Sequent] = {
      println("\n\nAPPLY\n")
      l.filter(socc => {
        if(socc.antecedent.size == socc.succedent.size) {
          val ant = socc.antecedent//.map(fo => fo.formula)
          val suc = socc.succedent//.map(fo => fo.formula)
          val b = ant.intersect(suc).isEmpty
          println("\n\nb = "+b+ "    so="+socc.toString)
          b
        }
        else
          true
      })
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


    def getCorrespondingFOcc(fo: FormulaOccurrence, from: List[SequentOccurrence]): FormulaOccurrence = from match {
      case so::rest if so.antecedent.contains(fo) => { if(so.succedent.size==1) so.succedent.head else new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}}
      case so::rest if so.succedent.contains(fo) =>  { if(so.antecedent.size==1) so.antecedent.head else new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}}
      case so::rest => getCorrespondingFOcc(fo, rest)
      case List() => new FormulaOccurrence(And(fo.formula,fo.formula), List())  with PointerOccurrence {def factory = fo.factory}
    }

    def getAllCorrespondingFOccs(lFOcc: List[FormulaOccurrence], from: List[SequentOccurrence]): List[FormulaOccurrence] = lFOcc.map(x => getCorrespondingFOcc(x,from))

    def getAllCorrFOccs(lFOcc: List[FormulaOccurrence], p: LKProof) =   getAllCorrespondingFOccs(lFOcc, apply(p))
  }



/////////////////////////////////////////////   Struct for the profile   ////////////////////////////////////
  trait Struct

  case class Times(left: Struct, right: Struct, auxFOccs: List[FormulaOccurrence]) extends Struct
  case class Plus(left: Struct, right: Struct) extends Struct
  case class Dual(sub: Struct) extends Struct
  case class A(formula: FormulaOccurrence) extends Struct // Atomic Struct
  case class EmptyTimesJunction() extends Struct
  case class EmptyPlusJunction() extends Struct

  object StructCreators {

    def extract(p: LKProof) : Struct = extract( p, getCutAncestors( p ) )

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
      so match {
        case lso : LabelledSequentOccurrence if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 => {
          val left = lso.l_antecedent.toList.head
          val right = lso.l_succedent.toList.head
          val ant = if ( cut_occs.contains( left ) )
                      Dual( A( new LabelledFormulaOccurrence( left.formula, Nil, right.skolem_label ) ) )::Nil
                    else
                      Nil
          val suc = if ( cut_occs.contains( right ) )
                      A( new LabelledFormulaOccurrence( right.formula, Nil, left.skolem_label ) )::Nil
                    else
                      Nil
          makeTimesJunction( ant:::suc )
        }
        case _ => {
//          println("\n\nERROR in the input\n")
          val cutAncInAntecedent = so.antecedent.toList.filter(x => cut_occs.contains(x)).map(x => Dual(A(x)))   //
          val cutAncInSuccedent = so.succedent.toList.filter(x => cut_occs.contains(x)).map(x => A(x))
          makeTimesJunction(cutAncInAntecedent:::cutAncInSuccedent)
        }
      }
      case UnaryLKProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) =>
        handleBinary( upperProofLeft, upperProofRight, aux1::aux2::Nil, cut_occs )
      case UnaryLKskProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
    }

    def handleUnary( upperProof: LKProof, cut_occs: Set[FormulaOccurrence] ) = extract(upperProof, cut_occs)

    def handleBinary( upperProofLeft: LKProof, upperProofRight: LKProof, l: List[FormulaOccurrence], cut_occs: Set[FormulaOccurrence] ) = {
      if (cut_occs.contains(l.head))
        Plus(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
      else
        Times(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs), l)
    }

    def makeTimesJunction(structs: List[Struct]):Struct = structs match {
      case Nil => EmptyTimesJunction()
      case s1::Nil => s1
      case s1::s2::Nil => Times(s1,s2,List())
//      case _ =>  assert(structs.size == 2).asInstanceOf[Struct]
      case s1::tail => Times(s1, makeTimesJunction(tail), List())
//      case s1::tail => new Times() with Labeled {type T = LKProof, def label: LKProof =  }
    }
  }
}