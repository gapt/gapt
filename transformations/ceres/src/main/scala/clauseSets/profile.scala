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
      case _ => {println("\n\nERROR in getListOfFOccsInStruct");List()}
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

           //gets from the axioms those formula occurrences which are ancestors of fo
  object getAncAx {
    def apply(fo: FormulaOccurrence, p: LKProof): List[FormulaOccurrence] = fo.ancestors match {
      case List() if getAllAxioms.isFOccInAxiom(fo, getAllAxioms.apply(p)) => fo::Nil
      case _ => fo.ancestors.foldLeft(List[FormulaOccurrence]())((x,y) => x:::apply(y,p))
    }
  }



  class proofProfile(val proof: LKProof) {

    var step = 1
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
        case Plus(s1,s2) => {
          print("\n                  +  \n")
          val (s11,s22) = (normalize(s1),normalize(s2))

//          val emp1 = s11 match {
//          case e1: EmptyPlusJunction => {println("\n\nEMPTY1\n\n"); true}
//          case e2: EmptyTimesJunction => {println("\n\nEMPTY2\n\n"); true}
//          case _ => false
//        }
//        val emp2 = s22 match {
//          case e1: EmptyPlusJunction => {println("\n\nEMPTY3\n\n"); true}
//          case e2: EmptyTimesJunction => {println("\n\nEMPTY4\n\n"); true}
//          case _ => false
//        }
//        if(emp1 && emp2)
//          return EmptyPlusJunction()
//        if(emp1)
//          return s22
//        if(emp2)
//          return s11

        Plus(s11,s22)
//        Plus(normalize(s1),normalize(s2))
      }
      case Times(s1,s2,auxFOccs) => {
                          print("\n                  x  \n")
        val (str1,str2) = (normalize(s1), normalize(s2))
//        print("\n\nimmediately Times:  "+printStruct(str1)+"  x  "+printStruct(str2))

//        val emp1 = str1 match {
//        case EmptyPlusJunction() => {println("\n\nEMPTY5\n\n"); true}
//        case EmptyTimesJunction() => {println("\n\nEMPTY6\n\n"); true}
//        case _ => false
//        }
//        val emp2 = str2 match {
//          case EmptyPlusJunction() => {println("\n\nEMPTY7\n\n"); true}
//          case EmptyTimesJunction() => {println("\n\nEMPTY8\n\n"); true}
//          case _ => false
//        }
//        if(emp1 && emp2)
//          return {print("\n emp1 && emp2\n");EmptyTimesJunction()}
//        if(emp1)
//          return {print("\n emp1 is empty \n");str2}
//        if(emp2)
//          return {print("\n  emp2 is empty\n");str1}
  //        println("\n\nThe struct x : ")
  //        printStruct(struct)
  //        println("\n\nstr1 : ")
  //        printStruct(str1)
  //        println("\n\nstr2 : ")
  //        printStruct(str2)
          merge(str1, str2, auxFOccs)
      }
      case s: A => {print("\n                 3  \n");s}
      case Dual(sub) => {print("\n                   4  \n");Dual(normalize(sub))}
      case e: EmptyTimesJunction => {print("\n          5  \n");e}
      case e: EmptyPlusJunction => {print("\n           6  \n");e}
    }

    def transformStructToProfile(struct:Struct) = clausify(normalize(struct))

//    def transformStructToLabelledClauseSet(struct:Struct) =
//      transformStructToClauseSet(struct).map( so => sequentOccurrenceToLabelledSequentOccurrence( so ) )

    private def transformProfiledCartesianProductToStruct(cp: List[Pair[Struct,Struct]]): Struct = cp match {
      case Pair(i,j)::Nil => Times(i, j, List[FormulaOccurrence]())
      case Pair(i,j)::rest => Plus(Times(i,j, List[FormulaOccurrence]()),transformProfiledCartesianProductToStruct(rest))
      //case Nil => { /*println("\nERROR in transformProfiledCartesianProductToStruct");*/EmptyPlusJunction()  }
    }
//      def transformNotProfiledCartesianProductToStruct(cp: List[Struct]): Struct = cp.foldLeft(EmptyPlusJunction())((x,y)=>Plus(x,y))
    private def transformNotProfiledCartesianProductToStruct(cp: List[Struct]): Struct = cp match {
      case i::Nil => i
      case i::rest => Plus(i,transformNotProfiledCartesianProductToStruct(rest))
     // case Nil => { /*println("\nERROR in transformNotProfiledCartesianProductToStruct");*/EmptyPlusJunction()  }
    }



    def isRedStruct(s: Struct, anc_OfauxFOccs: List[FormulaOccurrence]): Boolean = !(getListOfFOccsInStruct(s).intersect(anc_OfauxFOccs)).isEmpty



    private def merge(s1:Struct, s2:Struct, auxFOccs: List[FormulaOccurrence]):Struct = {

      val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))

      if(list1.size==0 || list2.size==0)
        println("ERROR, sizes = 0")



      if(list1.size==1 && list2.size==1)
        return Times(s1,s2,auxFOccs)
//      println("\n\n\n\n\n\nlist1.head : "+ printStruct(list1.head))
//      println("\n\nlist2.head : "+ printStruct(list2.head))

//      def correspFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x:::getAncAx(y)), proof)

      def ancOfAuxFOccs = getAllAxioms.getAllCorrFOccs(auxFOccs.foldLeft(List[FormulaOccurrence]())((x,y) => x ::: getAncAx(y, proof)), proof)

      val black_list1 = list1.filter(s => !isRedStruct(s, ancOfAuxFOccs))
      val red_list1 = list1.filter(s => isRedStruct(s, ancOfAuxFOccs))
      val black_list2 = list2.filter(s => !isRedStruct(s, ancOfAuxFOccs))
      val red_list2 = list2.filter(s => isRedStruct(s, ancOfAuxFOccs))

//      println("\n\n\n\n\n1\ns1 : "+ printStruct(s1))
//      println("\n\ns2 : "+ printStruct(s2))

//      println("\n2\n\n\nauxFOccs = "+auxFOccs.map(x => {print(", "+x.id);x.formula}).toString)

//      println("\ngetListOfFOccsInStruct(i) = "+getListOfFOccsInStruct(list1.head))

//      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getListOfFOccsInStruct(i).intersect(correspFOccs)).isEmpty && !(getListOfFOccsInStruct(j).intersect(correspFOccs)).isEmpty) yield (i,j)
//      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getListOfFOccsInStruct(i).intersect(ancOfAuxFOccs)).isEmpty && !(getListOfFOccsInStruct(j).intersect(ancOfAuxFOccs)).isEmpty) yield (i,j)

      val profiledCartesianProduct = for (i <- red_list1; j <- red_list2) yield (i,j)
      val notProfiledCartesianProduct = black_list1 ::: black_list2
//      println("\n\nprofiledCartesianProduct = "+profiledCartesianProduct.toString + "    "+profiledCartesianProduct.size)

//      println("\n\n-----------------merge:")
//      println("\n (list1,list2) = "+list1.size+"     size = "+list2.size)
      println("\nmerge : \n"+printStruct(Times(s1,s2,List())) + "\n auxFOccs = ")
      auxFOccs.foreach(x => {print("  "+x.formula.toStringSimple)+" ; "})

      println("\n\nCorresp. axioms:\n")
      ancOfAuxFOccs.foreach(fo => {println();getAncAx(fo,proof).foreach( axocc => print(axocc.formula.toStringSimple+" ; "))})

      println("\n\nRED,  size = "+profiledCartesianProduct.size)
      profiledCartesianProduct.foreach(x => {print(printStruct(x._1)+" x "+printStruct(x._2))})

//      val notProfiledCartesianProduct = for (i <- list1++list2; if !(profiledCartesianProduct.map(x => x._1).contains(i)) && !(profiledCartesianProduct.map(x => x._2).contains(i))) yield i
      println("\n\nBLACK,  size = "+notProfiledCartesianProduct.size)
      notProfiledCartesianProduct.foreach(x => {print(printStruct(x)+"  +  ") })

//      println("\n\nnotProfiledCartesianProduct = "+notProfiledCartesianProduct.toString + "    "+notProfiledCartesianProduct.size)

//      val profiledCartesianProduct = for (i <- list1; j <- list2; if !(getLabelsOfStruct(i).intersect(endSeqAuxFOccsLabels(proof))).isEmpty && !(getLabelsOfStruct(j).intersect(endSeqAuxFOccsLabels(proof))).isEmpty) yield (i,j)
//      val notProfiledCartesianProduct = for (i <- list1++list2; if !(profiledCartesianProduct.map(x => x._1).contains(i)) && !(profiledCartesianProduct.map(x => x._2).contains(i))) yield i

      if (profiledCartesianProduct.size > 0 ) // rewrite
      {
        val str2 = transformProfiledCartesianProductToStruct(profiledCartesianProduct)
//      println("\n\nstr2 = "+printStruct(str2))
        if (notProfiledCartesianProduct.size > 0)
        {
          val str1 = transformNotProfiledCartesianProductToStruct(notProfiledCartesianProduct)
//      println("\n\nstr1 = "+printStruct(str1))


//      if(notProfiledCartesianProduct.size == 0 || profiledCartesianProduct.size == 0)
//        return Times(s1 , s2 , auxFOccs)

//      val b1 = str1 match{
//        case e: EmptyPlusJunction => true
//        case e: EmptyTimesJunction => true
//        case _=> false
//      }
//
//      val b2 = str2 match{
//        case e: EmptyPlusJunction => true
//        case e: EmptyTimesJunction => true
//        case _ => false
//      }
//
//      if(b1)
//        return s2
//      else
//        if(b2)
//          return s1
//        else
//        println("\n\nERROR in merge")
//      println("\n\nmerge = "+printStruct(str2))
//      println("\n\n--------------end merge---")
          println("\n\nwe return " + printStruct(Plus(str1, str2)))
          Plus(str1, str2)
        } else {
          println("\n\nwe return " + printStruct(str2))
          str2
        }
      } else {
        println("we return " + printStruct(Times(s1, s2, auxFOccs)))
        Times(s1, s2, auxFOccs)
      }
    }

  // Defines the "big plus" used in Bruno's thesis
   object PlusN {
     def apply( ss: List[Struct] ) : Struct = ss match {
       case x::Nil => x
       case x::l => Plus( x, apply( l ) )
       case Nil => EmptyPlusJunction()
     }

     def unapply(s: Struct) = s match {
       case Plus(l, r) => Some( rec(s) )
       case _ => None
     }

     private def rec(s: Struct) : List[Struct] = s match {
       case Plus( l, r ) => rec(l):::rec(r)
       case _ => s::Nil
     }
   }

    private def getTimesJunctions(struct: Struct):List[Struct] = struct match {
      case s: Times => s::Nil
      case s: EmptyTimesJunction => s::Nil
      case s: A => s::Nil
      case s: Dual => s::Nil
      //case s: EmptyPlusJunction => Nil
      case Plus(s1,s2) => getTimesJunctions(s1):::getTimesJunctions(s2)
//      case Plus(s1,s2) => s1::s2::Nil
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
//      println("\n\nAPPLY\n")
      l.filter(socc => {
        if(socc.antecedent.size == socc.succedent.size) {
          val ant = socc.antecedent//.map(fo => fo.formula)
          val suc = socc.succedent//.map(fo => fo.formula)
          val b = ant.intersect(suc).isEmpty
//          println("\n\nb = "+b+ "    so="+socc.toString)
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