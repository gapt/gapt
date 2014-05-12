// --------------------- substitution begin

package at.logic.algorithms.shlk

import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema._
import at.logic.language.schema.IndexedPredicate._
import scala.xml._
import at.logic.calculi.slk._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
import at.logic.calculi.lksk.{Axiom => LKskAxiom,
WeakeningLeftRule => LKskWeakeningLeftRule,
WeakeningRightRule => LKskWeakeningRightRule,
ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}

import scala.collection.immutable.HashMap

import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.{HOLFormula}
import scala.Predef._
import at.logic.calculi.lk.propositionalRules._

//import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
//import at.logic.language.schema.SchemaSubstitution


//working version
//object applySchemaSubstitution2 {
//  def handleSchemaEquivalenceRule ( new_parent: LKProof,
//                                    subst: SchemaSubstitution1[HOLExpression],
//                                    old_parent: LKProof,
//                                    old_proof: LKProof,
//                                    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
//                                    m: FormulaOccurrence
//                                    ) = {
//      val new_proof = constructor( new_parent, subst(m.formula).asInstanceOf[HOLFormula])
//      new_proof
//  }
//
//  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
//  def handleWeakening( new_parent: LKProof,
//                       subst: SchemaSubstitution1[HOLExpression],
//                       old_parent: LKProof,
//                       old_proof: LKProof,
//                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
//                       m: FormulaOccurrence ) = {
//     val new_proof = constructor( new_parent, subst(m.formula).asInstanceOf[HOLFormula] )
//     new_proof
//  }
//  def handleContraction( new_parent: LKProof,
//                         subst: SchemaSubstitution1[HOLExpression],
//                         old_parent: LKProof,
//                         old_proof: LKProof,
//                         a1: FormulaOccurrence,
//                         a2: FormulaOccurrence,
//                        constructor: (LKProof, HOLFormula, dbTRS) => LKProof, trs: dbTRS) = {
//
////    println("n = "+subst.map.toList.head._2)
////    println("\n\nContrL:")
////    println("aux = "+subst(a1.formula))
////    println("seq = "+new_parent.root)
//    constructor( new_parent, subst(a1.formula).asInstanceOf[HOLFormula], trs )
////    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
//  }
//  def handleBinaryProp( new_parent_1: LKProof,
//                        new_parent_2: LKProof,
//                        subst: SchemaSubstitution1[HOLExpression],
//                        a1: FormulaOccurrence,
//                        a2: FormulaOccurrence,
//                        old_parent_1: LKProof,
//                        old_parent_2: LKProof,
//                        old_proof: LKProof,
//                        constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) = {
//
//     constructor( new_parent_1, new_parent_2, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula] )
//  }
//
//
//
//  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: SchemaSubstitution1[HOLExpression], trs: dbTRS ) : LKProof = {
//    implicit val factory = defaultFormulaOccurrenceFactory
//    proof match {
//
//      case Axiom(ro) => {
//        val a = Axiom(ro.antecedent.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]),ro.succedent.toList.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]))
////        val ant_occs = a._1.root.antecedent.toList
////        val succ_occs = a._1.root.succedent.toList
//        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
////        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
////        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
////        println("ax : "+a.root)
//        a
//      }
//      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
//      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
//      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionLeftRule.apply, trs )
//      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionRightRule.apply, trs)
//      case CutRule(p1, p2, s, a1, a2) => {
//        val new_p1 = new_parents.head
//        val new_p2 = new_parents.last
////        println("Cut:")
////        println(new_p1.root)
////        println("aux = "+subst( a1.formula ))
////        println(new_p2.root)
//        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
//        val new_proof = sCutRule( new_p1, new_p2, subst( a1.formula ).asInstanceOf[HOLFormula], trs )
//    //    ( new_proof, computeMap(
//     //     p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
//      //    proof, new_proof, new_p1._2 ++ new_p2._2 ) )
//        new_proof
//      }
//      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )
//
//      case AndLeft1Rule(p, s, a, m) => {
//        val f = m.formula match { case And(_, w) => w }
//        val new_parent = new_parents.head
////        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
//        val new_proof = AndLeft1Rule( new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula] )
//        new_proof
//      }
//      case AndLeft2Rule(p, s, a, m) => {
//        val f = m.formula match { case And(w, _) => w }
//        val new_parent = new_parents.head
////        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
//        val new_proof = AndLeft2Rule( new_parent, subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula], subst(a.formula).asInstanceOf[HOLFormula] )
//        new_proof
//      }
//  //    case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
//
//      case OrRight1Rule(p, s, a, m) => {
//        val f = m.formula match {
//          case Or(_, w) => w
//          case _ => throw new Exception("Error in OrRight1Rule in unfoldSIND.scala")
//        }
//        val new_parent = new_parents.head
////        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
//        val new_proof = OrRight1Rule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula], subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula] )
//        new_proof
//      }
//      case OrRight2Rule(p, s, a, m) => {
//        val f = m.formula match {
//          case Or(w, _) => w
//          case _ => throw new Exception("Error in OrRight2Rule in unfoldSIND.scala")
//        }
//        val new_parent = new_parents.head
//        val new_proof = OrRight2Rule( new_parent, subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula], subst( a.formula ).asInstanceOf[HOLFormula] )
//        new_proof
//      }
//      case NegLeftRule(p, s, a, m) => {
//        val new_parent = new_parents.head
//      //  val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
//        val new_proof = NegLeftRule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula] )
// //       ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
//        new_proof
//      }
//      case NegRightRule(p, s, a, m) => {
//        val new_parent = new_parents.head
//        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
//        //val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
//        val new_proof = NegRightRule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula] )
//   //     ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
//        new_proof
//      }
//      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
//        val new_parent1 = new_parents.head
//        val new_parent2 = new_parents.last
//        println("a1 = "+printSchemaProof.formulaToString(a1.formula) )
//        println("a2 = "+printSchemaProof.formulaToString(a2.formula) )
//        println("m = "+printSchemaProof.formulaToString(m.formula) )
//        println("subst a1 = "+printSchemaProof.formulaToString(subst(a1.formula).asInstanceOf[HOLFormula]) )
//        println("subst a2 = "+printSchemaProof.formulaToString(subst(a2.formula).asInstanceOf[HOLFormula]) )
//        println("\nnewparent1 = "+printSchemaProof(new_parent1))
//        println("\nnewparent2 = "+printSchemaProof(new_parent2))
//        ImpLeftRule(new_parent1, new_parent2, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula])
//      }
//      case ImpRightRule(p, s, a1, a2, m) => {
//        val new_parent = new_parents.head
//        ImpRightRule(new_parent, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula])
//      }
//      case ForallLeftRule(p, seq, a, m, t) => {
//        val new_parent = new_parents.head
//        ForallLeftRule(new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst(m.formula).asInstanceOf[HOLFormula], subst(t))
//      }
//      case ForallRightRule(p, seq, a, m, v) => {
//        val new_parent = new_parents.head
//        ForallRightRule(new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst(m.formula).asInstanceOf[HOLFormula], subst(v).asInstanceOf[HOLVar])
//      }
//    }
//  }
//
////  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : LKProof = {
////     subst.map.toList.head._2 match {
////        case IntZero() => CloneLKProof2(schema.base)
////        case _ => apply(schema.rec, subst)
////     }
////  }
//
//
//  //************************************************************************************
//  def apply( proof_name: String, number: Int, trs: dbTRS ): LKProof = {
//    if (number < 1) {
//      println("\nproof_name = "+proof_name)
//      println("number = "+number)
//
////      RemoveEqRulesFromGroundSchemaProof(SchemaProofDB.get(proof_name).base)
//      SchemaProofDB.get(proof_name).base
//    }
//    else {
//      println("\nproof_name = "+proof_name)
//      println("number = "+number)
//      val k = IntVar(new VariableStringSymbol("k")) ;
//      val new_map = Map[Var, HOLExpression]() + Pair(k, toIntegerTerm(number-1))
//      val subst = new SchemaSubstitution1[HOLExpression](new_map)
////      RemoveEqRulesFromGroundSchemaProof(apply(SchemaProofDB.get(proof_name).rec, subst, number))
//      apply(SchemaProofDB.get(proof_name).rec, subst, number, trs)
//    }
//  }
//
//  def toIntegerTerm(i: Int): IntegerTerm = {
//    if (i == 0)
//      IntZero()
//    else
//      Succ(toIntegerTerm(i-1))
//  }
//
//  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] , cnt: Int, trs: dbTRS) : LKProof = {
////    println("\n"+proof.rule)
////    println("cnt = "+cnt)
//
//    proof match {
//      case SchemaProofLinkRule( seq, link, ind::_ ) => {
//        println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
//          val new_ind = subst(ind)
//
//          //subst.map.toList.foreach(p => println(p._1,p._2))
//          //subst.map.head._2 match {
//
//
//          if (cnt == 0)
//            CloneLKProof2(SchemaProofDB.get(link).base, trs)
//      /*    new_ind match {
//          case IntZero() => {
//                    // val res = (CloneLKProof2(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
//                    val res = CloneLKProof2(SchemaProofDB.get(link).base)
//     //               printSchemaProof(res._1)
//                    res
//          } */
//
//          else
//            if (cnt == 1) {
//
////                apply(SchemaProofDB.get(link), new_subst, cnt1)
//              new_ind match {
//                case y:IntZero => {
////                println("\nnew_ind = "+0)
//                CloneLKProof2(SchemaProofDB.get(link).base, trs)
//                }
//                case _ => {
////                println("\nnew_ind > "+0)
//                apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]), trs)
////                CloneLKProof2(SchemaProofDB.get(link).base)
//                }
//              }
//            }
//            else {
//              if(StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]) == cnt) {
//                apply(SchemaProofDB.get(link).rec, subst, cnt, trs)
//              }
//              else {
//                val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Pair(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
//                val new_subst = new SchemaSubstitution1(new_map)
//  //              val cnt1 = cnt - 1
//                apply(SchemaProofDB.get(link).rec, new_subst, cnt-1, trs)
//              }
//            }
//
//      //      }
// //           apply(SchemaProofDB.get(link), new_subst)
//
//      }
//
//      case AndEquivalenceRule1(up, r, aux, main) =>  {
//    //    println("\n UnaryProof AndEquivalenceRule1: "+printSchemaProof.sequentToString(r))
//        val up1 = apply(up, subst, cnt, trs)
//   //     println("\n"+proof.rule+")")
//   //     println("\n aux = "+printSchemaProof.formulaToString(subst(aux.formula)))
//
//   //     println("\nAndEquivalenceRule1 up1: "+printSchemaProof.sequentToString(up1.root))
//        AndEquivalenceRule1(up1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
//      }
//
//      case OrEquivalenceRule1(up, r, aux, main) =>  {
////        println("\n UnaryProof OrEquivalenceRule1: "+printSchemaProof.sequentToString(r))
//        OrEquivalenceRule1(apply(up, subst, cnt, trs), subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
//      }
//
//      case trsArrowRule(up, r, aux, _) =>  {
//        trsArrowRule(apply(up, subst, cnt, trs), subst(aux.formula).asInstanceOf[HOLFormula], trs)
//      }
//
//      case Axiom(_) => {
////        println("\n"+proof.rule)
//        val res = handleRule( proof, Nil, subst, trs )
////        println("\nafter : "+res.rule)
//        res
//      }
//      case UnaryLKProof(_, p, _, _, _) => {
////        println("\n"+proof.rule)
//        val res = handleRule( proof, apply( p, subst, cnt, trs )::Nil, subst, trs )
////        println("\nafter : "+res.rule)
//        res
//      }
//
//      case OrLeftRule(p1, p2, s, a1, a2, m) => {
////        println("\n"+proof.rule)
//        val pr1 = apply( p1, subst, cnt, trs )
//        val pr2 = apply( p2, subst, cnt, trs )
//   //     println("\n"+proof.rule)
//    //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
//     //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
//      //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
//        val res = handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
////        println("\nafter : "+res.rule)
//        res
//      }
//
//      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
////        println("\n"+proof.rule)
//        val res = handleRule( proof, apply( p1, subst, cnt, trs )::apply( p2, subst, cnt, trs )::Nil, subst, trs )
////        println("\nafter : "+res.rule)
//        res
//      }
//      case _ => {println("\n\n\nERROR in apply schema substitution\n"); proof}
//    }
//  }
//}


//working version
//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
//uses t.r.s. !!!
//object CloneLKProof2 {
//  import at.logic.language.hol._
//
//  def apply(p: LKProof, trs: dbTRS):LKProof = {
//    println("\nCloneLKProof2 : "+p.rule)
//    p match {
//      case trsArrowLeftRule(p, s, a, m) => {
//        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//        val new_p = apply(p, trs)
//        trsArrowLeftRule(new_p, a.formula, trs)
//      }
//      case trsArrowRightRule(p, s, a, m) => {
//        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//        val new_p = apply(p, trs)
//        trsArrowRightRule(new_p, a.formula, trs)
//      }
//
//      case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))
//
//      case AndLeftEquivalenceRule1(p, s, a, m) => {
//        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//        val new_p = apply(p, trs)
//        AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case AndRightEquivalenceRule1(p, s, a, m) => {
//        // println("\nAndRightEquivalenceRule1\n")
//        val new_p = apply(p, trs)
//        AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case OrRightEquivalenceRule1(p, s, a, m) => {
//        // println("\nOrRightEquivalenceRule1\n")
//        val new_p = apply(p, trs)
//        OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case AndLeftEquivalenceRule3(p, s, a, m) => {
//        // println("\nAndLeftEquivalenceRule3\n")
//        val new_p = apply(p, trs)
//        AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case AndRightEquivalenceRule3(p, s, a, m) => {
//        // println("\nAndRightEquivalenceRule3\n")
//        val new_p = apply(p, trs)
//        AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case OrRightEquivalenceRule3(p, s, a, m) => {
//        //println("\nOrRightEquivalenceRule3\n")
//        val new_p = apply(p, trs)
//        OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
//      }
//
//      case WeakeningLeftRule(p, _, m) => {
//        val new_p = apply(p, trs)
//        implicit val factory = defaultFormulaOccurrenceFactory
//        WeakeningLeftRule( new_p, m.formula )
//      }
//
//      case WeakeningRightRule(p, _, m) => {
//        val new_p = apply(p, trs)
//        implicit val factory = defaultFormulaOccurrenceFactory
//        WeakeningRightRule( new_p, m.formula )
//      }
//
//      case CutRule( p1, p2, _, a1, a2 ) => {
//        val new_p1 = apply(p1, trs)
//        val new_p2 = apply(p2, trs)
//        CutRule(new_p1, new_p2, a2.formula)
//      }
//
//      case OrLeftRule(p1, p2, _, a1, a2, m) => {
//        val new_p1 = apply(p1, trs)
//        val new_p2 = apply(p2, trs)
//        OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
//      }
//
//      case AndRightRule(p1, p2, _, a1, a2, m) => {
//        val new_p1 = apply(p1, trs)
//        val new_p2 = apply(p2, trs)
//        AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
//      }
//
//      case NegLeftRule( p, _, a, m ) => {
//        val new_p = apply(p, trs)
//        NegLeftRule( new_p, a.formula )
//      }
//
//      case AndLeft1Rule(p, r, a, m) =>  {
//        val new_p = apply(p, trs)
//        val a2 = m.formula  match { case And(l, right) => right }
//        //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
//        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
//        //    println(printSchemaProof.formulaToString(a2))
//        AndLeft1Rule( new_p, a.formula, a2)
//      }
//
//      case AndLeft2Rule(p, r, a, m) =>  {
//        val new_p = apply(p, trs)
//        val a2 = m.formula  match { case And(l, _) => l }
//        //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
//        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
//        //     println(printSchemaProof.formulaToString(a2))
//        AndLeft2Rule( new_p, a2, a.formula )
//      }
//
//      case OrRight1Rule(p, r, a, m) =>  {
//        val new_p = apply(p, trs)
//        val a2 = m.formula  match { case Or(_, r) => r }
//        //            println("\np or:r1 = "+p.root)
//        //            println("\nnew_p or:r1 = "+new_p.root)
//        //            println("\nor:r1 a = "+a.formula)
//        //            println("\nor:r1 m = "+m.formula)
//        OrRight1Rule( new_p, a.formula, a2)
//      }
//
//      case OrRight2Rule(p, r, a, m) =>  {
//        val new_p = apply(p, trs)
//        val a2 = m.formula  match { case Or(l, _) => l }
//        //            println("\np or:r2 = "+p.root)
//        //            println("\nnew_p or:r2 = "+new_p.root)
//        //          println("\nor:r2 a = "+a.formula)
//        //            println("\nor:r2 m = "+m.formula)
//        OrRight2Rule( new_p, a2, a.formula)
//      }
//
//      case NegRightRule( p, _, a, m ) => {
//        val new_p = apply(p, trs)
//        NegRightRule( new_p, a.formula )
//      }
//
//      case ContractionLeftRule(p, _, a1, a2, m) => {
//        val new_p = apply(p, trs)
//        ContractionLeftRule( new_p, a1.formula )
//      }
//
//      case ContractionRightRule(p, _, a1, a2, m) => {
//        val new_p = apply(p, trs)
//        //            println("\nc:r = "+new_p.root)
//        ContractionRightRule( new_p, a1.formula )
//      }
//
//      case ForallLeftRule(p, seq, a, m, t) => {
//        val new_parent = apply(p, trs)
//        ForallLeftRule(new_parent, a.formula, m.formula, t)
//      }
//      case ForallRightRule(p, seq, a, m, v) => {
//        val new_parent = apply(p, trs)
//        ForallRightRule(new_parent, a.formula, m.formula, v)
//      }
//
//      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
//        val new_parent1 = apply(p1, trs)
//        val new_parent2 = apply(p2, trs)
//        ImpLeftRule(new_parent1, new_parent2, a1.formula, a2.formula)
//      }
//      case ImpRightRule(p, s, a1, a2, m) => {
//        val new_parent = apply(p, trs)
//        ImpRightRule(new_parent, a1.formula, a2.formula)
//      }
//      case _ => { println("ERROR in CloneLKProof2 : missing rule!");throw new Exception("ERROR in unfolding: CloneLKProof2: missing rule !\n") }
//    }}
//}


//test version
object applySchemaSubstitution2 {
  def handleSchemaEquivalenceRule ( new_parent: LKProof,
                                    subst: SchemaSubstitution1[HOLExpression],
                                    old_parent: LKProof,
                                    old_proof: LKProof,
                                    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                                    m: FormulaOccurrence
                                    ) = {
    val new_proof = constructor( new_parent, subst(m.formula).asInstanceOf[HOLFormula])
    new_proof
  }

  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
  def handleWeakening( new_parent: LKProof,
                       subst: SchemaSubstitution1[HOLExpression],
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
    val new_proof = constructor( new_parent, unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]) )
    new_proof
  }
  def handleContraction( new_parent: LKProof,
                         subst: SchemaSubstitution1[HOLExpression],
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         constructor: (LKProof, HOLFormula) => LKProof) = {

    //    println("n = "+subst.map.toList.head._2)
    //    println("\n\nContrL:")
    //    println("aux = "+subst(a1.formula))
    //    println("seq = "+new_parent.root)
    constructor( new_parent, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]) )
    //    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }
  def handleBinaryProp( new_parent_1: LKProof,
                        new_parent_2: LKProof,
                        subst: SchemaSubstitution1[HOLExpression],
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) = {

    constructor( new_parent_1, new_parent_2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]) )
  }



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: SchemaSubstitution1[HOLExpression] ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => {
        val a = Axiom(ro.antecedent.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])),ro.succedent.toList.map(fo => unfoldSFormula(subst(fo.formula).asInstanceOf[HOLFormula])))
        //        val ant_occs = a._1.root.antecedent.toList
        //        val succ_occs = a._1.root.succedent.toList
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        //        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
        //        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
        //        println("ax : "+a.root)
        a
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m)
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionRightRule.apply)
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        //        println("Cut:")
        //        println(new_p1.root)
        //        println("aux = "+subst( a1.formula ))
        //        println(new_p2.root)
        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        val new_proof = sCutRule( new_p1, new_p2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]) )
        //    ( new_proof, computeMap(
        //     p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
        //    proof, new_proof, new_p1._2 ++ new_p2._2 ) )
        new_proof
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft1Rule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
        //        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
        val new_proof = AndLeft2Rule( new_parent, unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        new_proof
      }
      //    case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(_, w) => w
          case _ => throw new Exception("Error in OrRight1Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        //        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = OrRight1Rule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(w, _) => w
          case _ => throw new Exception("Error in OrRight2Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, unfoldSFormula(subst(f.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula] ) )
        new_proof
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
        //  val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegLeftRule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        //       ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        new_proof
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        //val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegRightRule( new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]) )
        //     ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        new_proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = new_parents.head
        val new_parent2 = new_parents.last
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = new_parents.head
        ImpRightRule(new_parent, unfoldSFormula(subst(a1.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(a2.formula).asInstanceOf[HOLFormula]))
      }
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = new_parents.head
//        print(Console.RED+new_parent.rule +" = "+Console.RESET)
//        println (printSchemaProof.sequentToString (new_parent.root))
//        println(Console.BLUE+"START"+Console.RESET)
//        printSchemaProof(new_parent)
//        println(Console.BLUE+"END"+Console.RESET)
//        println(Console.BLUE+printSchemaProof.formulaToString(unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula], trs))+Console.RESET)
//        println(Console.BLUE+printSchemaProof.formulaToString(unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula], trs)))
//        println(printSchemaProof.formulaToString(subst(t)))
//        println(printSchemaProof.formulaToString(unfoldSTerm(subst(t), trs))+Console.RESET)

        ForallLeftRule(new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]), unfoldSTerm(subst(t)))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = new_parents.head
//        println("\nnew_parent : "+printSchemaProof.sequentToString(new_parent.root))
//        println("aux : "+printSchemaProof.formulaToString(unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula], trs)))
//        println("m : "+printSchemaProof.formulaToString(unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula], trs)))
//        println("v : "+printSchemaProof.formulaToString(subst(v).asInstanceOf[HOLVar]))
        ForallRightRule(new_parent, unfoldSFormula(subst(a.formula).asInstanceOf[HOLFormula]), unfoldSFormula(subst(m.formula).asInstanceOf[HOLFormula]), subst(v).asInstanceOf[HOLVar])
      }
    }
  }

  //  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : LKProof = {
  //     subst.map.toList.head._2 match {
  //        case IntZero() => CloneLKProof2(schema.base)
  //        case _ => apply(schema.rec, subst)
  //     }
  //  }


  //************************************************************************************

  def apply( proof_name: String, number: Int ): LKProof = {
    if (number == 0) {
      //println("\nproof_name = "+proof_name)
      //println("number = "+number)
      CloneLKProof2(SchemaProofDB.get(proof_name).base)
    }
    else {
      //println("\nproof_name = "+proof_name)
      //println("number = "+number)
      val k = IntVar(new VariableStringSymbol("k")) ;
      val new_map = Map[Var, HOLExpression]() + Pair(k, toIntegerTerm(number-1))
      val subst = new SchemaSubstitution1[HOLExpression](new_map)
      //      RemoveEqRulesFromGroundSchemaProof(apply(SchemaProofDB.get(proof_name).rec, subst, number))
      apply(SchemaProofDB.get(proof_name).rec, subst, number)
    }
  }

  def toIntegerTerm(i: Int): IntegerTerm = {
    if (i == 0)
      IntZero()
    else
      Succ(toIntegerTerm(i-1))
  }

  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] , cnt: Int) : LKProof = {
        //println("\n"+proof.rule+" : "+printSchemaProof.sequentToString(proof.root))
    //    println("cnt = "+cnt)

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
        //println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
        val new_ind = subst(ind)

        //subst.map.toList.foreach(p => println(p._1,p._2))
        //subst.map.head._2 match {


        if (cnt == 0) {
          //println("cnt == 0")
          CloneLKProof2(SchemaProofDB.get(link).base)
        }

        /*    new_ind match {
       case IntZero() => {
                 // val res = (CloneLKProof2(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
                 val res = CloneLKProof2(SchemaProofDB.get(link).base)
  //               printSchemaProof(res._1)
                 res
       } */

        else
        if (cnt == 1) {
          //println("cnt == 1")
          //                apply(SchemaProofDB.get(link), new_subst, cnt1)
          new_ind match {
            case y:IntZero => {
              //                println("\nnew_ind = "+0)
              CloneLKProof2(SchemaProofDB.get(link).base)
            }
            case _ => {
              //                println("\nnew_ind > "+0)
              apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]))
              //                CloneLKProof2(SchemaProofDB.get(link).base)
            }
          }
        }
        else {
          if(StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]) == cnt) {
            apply(SchemaProofDB.get(link).rec, subst, cnt)
          }
          else {
            val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Pair(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
            val new_subst = new SchemaSubstitution1(new_map)
            //              val cnt1 = cnt - 1
            apply(SchemaProofDB.get(link).rec, new_subst, cnt-1)
          }
        }

        //      }
        //           apply(SchemaProofDB.get(link), new_subst)

      }

      case AndEquivalenceRule1(up, r, aux, main) =>  {
        //    println("\n UnaryProof AndEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        val up1 = apply(up, subst, cnt)
        //     println("\n"+proof.rule+")")
        //     println("\n aux = "+printSchemaProof.formulaToString(subst(aux.formula)))

        //     println("\nAndEquivalenceRule1 up1: "+printSchemaProof.sequentToString(up1.root))
        AndEquivalenceRule1(up1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
        //        println("\n UnaryProof OrEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        OrEquivalenceRule1(apply(up, subst, cnt), subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case trsArrowRule(up, r, aux, _) =>  {
        apply(up, subst, cnt)
//        trsArrowRule(apply(up, subst, cnt, trs), unfoldSFormula(subst(aux.formula).asInstanceOf[HOLFormula], trs), trs)
      }

      case Axiom(_) => {
        //        println("\n"+proof.rule)
        val res = handleRule( proof, Nil, subst )
        //        println("\nafter : "+res.rule)
        res
      }
      case UnaryLKProof(_, p, _, _, _) => {
        //        println("\n"+proof.rule)
        val res = handleRule( proof, apply( p, subst, cnt )::Nil, subst )
        //        println("\nafter : "+res.rule)
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        //        println("\n"+proof.rule)
        val pr1 = apply( p1, subst, cnt )
        val pr2 = apply( p2, subst, cnt )
        //     println("\n"+proof.rule)
        //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
        //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
        //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
        val res = handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply)
        //        println("\nafter : "+res.rule)
        res
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        //        println("\n"+proof.rule)
        val res = handleRule( proof, apply( p1, subst, cnt )::apply( p2, subst, cnt )::Nil, subst )
        //        println("\nafter : "+res.rule)
        res
      }
      case _ => throw new Exception("ERROR in apply schema substitution\n")
    }
  }
}


//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
//uses t.r.s. !!!
object CloneLKProof2 {
  import at.logic.language.hol._

  def apply(p: LKProof):LKProof = {
//    println("\nCloneLKProof2 : "+p.rule)
    p match {
      case trsArrowLeftRule(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//        val new_p = apply(p, trs)
//        trsArrowLeftRule(new_p, a.formula, trs)
        apply(p)
      }
      case trsArrowRightRule(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//        val new_p = apply(p, trs)
//        trsArrowRightRule(new_p, a.formula, trs)
        apply(p)
      }

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => unfoldSFormula(fo.formula.asInstanceOf[HOLFormula])),ro.succedent.map(fo => unfoldSFormula(fo.formula.asInstanceOf[HOLFormula])))

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
        val new_p = apply(p)
        AndLeftEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule1\n")
        val new_p = apply(p)
        AndRightEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        // println("\nOrRightEquivalenceRule1\n")
        val new_p = apply(p)
        OrRightEquivalenceRule1(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
        // println("\nAndLeftEquivalenceRule3\n")
        val new_p = apply(p)
        AndLeftEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule3\n")
        val new_p = apply(p)
        AndRightEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        //println("\nOrRightEquivalenceRule3\n")
        val new_p = apply(p)
        OrRightEquivalenceRule3(new_p, unfoldSFormula(a.formula.asInstanceOf[SchemaFormula]), unfoldSFormula(m.formula.asInstanceOf[SchemaFormula]))
      }

      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningLeftRule( new_p, unfoldSFormula(m.formula) )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningRightRule( new_p, unfoldSFormula(m.formula) )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        CutRule(new_p1, new_p2, unfoldSFormula(a2.formula))
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        OrLeftRule(new_p1, new_p2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        AndRightRule(new_p1, new_p2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }

      case NegLeftRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegLeftRule( new_p, unfoldSFormula(a.formula) )
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, right) => right }
        //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
        AndLeft1Rule( new_p, unfoldSFormula(a.formula), unfoldSFormula(a2))
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //     println(printSchemaProof.formulaToString(a2))
        AndLeft2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula) )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        //            println("\np or:r1 = "+p.root)
        //            println("\nnew_p or:r1 = "+new_p.root)
        //            println("\nor:r1 a = "+a.formula)
        //            println("\nor:r1 m = "+m.formula)
        OrRight1Rule( new_p, unfoldSFormula(a.formula), unfoldSFormula(a2))
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
        //            println("\np or:r2 = "+p.root)
        //            println("\nnew_p or:r2 = "+new_p.root)
        //          println("\nor:r2 a = "+a.formula)
        //            println("\nor:r2 m = "+m.formula)
        OrRight2Rule( new_p, unfoldSFormula(a2), unfoldSFormula(a.formula))
      }

      case NegRightRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegRightRule( new_p, unfoldSFormula(a.formula) )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionLeftRule( new_p, unfoldSFormula(a1.formula) )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        //            println("\nc:r = "+new_p.root)
        ContractionRightRule( new_p, unfoldSFormula(a1.formula) )
      }

      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallLeftRule(new_parent, unfoldSFormula(a.formula), unfoldSFormula(m.formula), unfoldSTerm(t))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = apply(p)
        ForallRightRule(new_parent, unfoldSFormula(a.formula), unfoldSFormula(m.formula), v)
      }

      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = apply(p1)
        val new_parent2 = apply(p2)
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = apply(p)
        ImpRightRule(new_parent, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }
      case _ => throw new Exception("ERROR in unfolding: CloneLKProof2: missing rule !\n")
    }}
}






//removes the arrow rules and unfolds the sTerms
//the proof does not contain proof-links
object LKrwToLK {
  def apply(p: LKProof): LKProof = {
    //println("\nLKrwToLK Rule : "+p.rule)
    //println(printSchemaProof.sequentToString(p.root))

    p match {
      case Axiom(seq) => Axiom(seq.antecedent.map(f => unfoldSFormula(f.formula)), seq.succedent.map(f => unfoldSFormula(f.formula)))
      case trsArrowLeftRule(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
        apply(p)
      }
      case trsArrowRightRule(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
        apply(p)
      }
      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningLeftRule( new_p, unfoldSFormula(m.formula) )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningRightRule( new_p, unfoldSFormula(m.formula) )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        CutRule(new_p1, new_p2, unfoldSFormula(a2.formula))
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        OrLeftRule(new_p1, new_p2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        AndRightRule(new_p1, new_p2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }

      case NegLeftRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegLeftRule( new_p, unfoldSFormula(a.formula))
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, right) => right }
        //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
        AndLeft1Rule( new_p, unfoldSFormula(a.formula), unfoldSFormula(a2.asInstanceOf[HOLFormula]))
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //     println(printSchemaProof.formulaToString(a2))
        AndLeft2Rule( new_p, unfoldSFormula(a2.asInstanceOf[HOLFormula]), unfoldSFormula(a.formula) )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        //            println("\np or:r1 = "+p.root)
        //            println("\nnew_p or:r1 = "+new_p.root)
        //            println("\nor:r1 a = "+a.formula)
        //            println("\nor:r1 m = "+m.formula)
        OrRight1Rule( new_p, unfoldSFormula(a.formula), unfoldSFormula(a2.asInstanceOf[HOLFormula]))
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
        //            println("\np or:r2 = "+p.root)
        //            println("\nnew_p or:r2 = "+new_p.root)
        //          println("\nor:r2 a = "+a.formula)
        //            println("\nor:r2 m = "+m.formula)
        OrRight2Rule( new_p, unfoldSFormula(a2.asInstanceOf[HOLFormula]), unfoldSFormula(a.formula))
      }

      case NegRightRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegRightRule( new_p, unfoldSFormula(a.formula) )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionLeftRule( new_p, unfoldSFormula(a1.formula) )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        //            println("\nc:r = "+new_p.root)
        ContractionRightRule( new_p, unfoldSFormula(a1.formula) )
      }
//(P(g(1, z(1))) ⊃ P(f(g(1, z(1)))))
//    (P(f(z(1)))⊃P(f(f(z(1)))))
//
//(P(g(1, z)) ⊃ P(f(g(1, z))) != P(f(z))⊃P(f(f(z))))
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallLeftRule(new_parent, unfoldSFormula(a.formula), unfoldSFormula(m.formula), unfoldSTerm(t))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = apply(p)
        ForallRightRule(new_parent, unfoldSFormula(a.formula), unfoldSFormula(m.formula), v)
      }

      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = apply(p1)
        val new_parent2 = apply(p2)
        ImpLeftRule(new_parent1, new_parent2, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = apply(p)
        ImpRightRule(new_parent, unfoldSFormula(a1.formula), unfoldSFormula(a2.formula))
      }
      case _ => throw new Exception("ERROR in rewriting: LKrwToLK: missing rule !\n"+p.rule) 
    }
  }
}
