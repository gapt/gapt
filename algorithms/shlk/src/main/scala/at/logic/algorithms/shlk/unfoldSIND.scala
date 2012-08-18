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

import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.{HOLFormula}
import scala.Predef._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules.ForallLeftRule._
import at.logic.calculi.lk.quantificationRules.ForallRightRule._
import at.logic.calculi.lk.propositionalRules.ImpLeftRule._
import at.logic.calculi.lk.propositionalRules.ImpRightRule._

//import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
//import at.logic.language.schema.SchemaSubstitution

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
     val new_proof = constructor( new_parent, subst(m.formula).asInstanceOf[HOLFormula] )
     new_proof
  }
  def handleContraction( new_parent: LKProof,
                         subst: SchemaSubstitution1[HOLExpression],
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                        constructor: (LKProof, HOLFormula, dbTRS) => LKProof, trs: dbTRS) = {

//    println("n = "+subst.map.toList.head._2)
    println("\n\nContrL:")
    println("aux = "+subst(a1.formula))
    println("seq = "+new_parent.root)
    constructor( new_parent, subst(a1.formula).asInstanceOf[HOLFormula], trs )
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

     constructor( new_parent_1, new_parent_2, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula] )
  }



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: SchemaSubstitution1[HOLExpression], trs: dbTRS ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => {
        val a = Axiom(ro.antecedent.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]),ro.succedent.toList.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]))
//        val ant_occs = a._1.root.antecedent.toList
//        val succ_occs = a._1.root.succedent.toList
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
//        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
//        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
//        println("ax : "+a.root)
        a
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionLeftRule.apply, trs )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, sContractionRightRule.apply, trs)
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        println("Cut:")
        println(new_p1.root)
        println("aux = "+subst( a1.formula ))
        println(new_p2.root)
        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        val new_proof = sCutRule( new_p1, new_p2, subst( a1.formula ).asInstanceOf[HOLFormula], trs )
    //    ( new_proof, computeMap(
     //     p1.root.antecedent ++ (p1.root.succedent - a1) ++ (p2.root.antecedent - a2) ++ p2.root.succedent,
      //    proof, new_proof, new_p1._2 ++ new_p2._2 ) )
        new_proof
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
//        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = AndLeft1Rule( new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula] )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
//        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
        val new_proof = AndLeft2Rule( new_parent, subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula], subst(a.formula).asInstanceOf[HOLFormula] )
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
        val new_proof = OrRight1Rule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula], subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula] )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match {
          case Or(w, _) => w
          case _ => throw new Exception("Error in OrRight2Rule in unfoldSIND.scala")
        }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, subst( f.asInstanceOf[HOLFormula] ).asInstanceOf[HOLFormula], subst( a.formula ).asInstanceOf[HOLFormula] )
        new_proof
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
      //  val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegLeftRule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula] )
 //       ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        new_proof
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        //val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
        val new_proof = NegRightRule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula] )
   //     ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
        new_proof
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_parent1 = new_parents.head
        val new_parent2 = new_parents.last
        ImpLeftRule(new_parent1, new_parent2, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula])
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = new_parents.head
        ImpRightRule(new_parent, subst(a1.formula).asInstanceOf[HOLFormula], subst(a2.formula).asInstanceOf[HOLFormula])
      }
      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = new_parents.head
        ForallLeftRule(new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst(m.formula).asInstanceOf[HOLFormula], subst(t))
      }
      case ForallRightRule(p, seq, a, m, v) => {
        val new_parent = new_parents.head
        ForallRightRule(new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst(m.formula).asInstanceOf[HOLFormula], subst(v).asInstanceOf[HOLVar])
      }
    }
  }

//  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : LKProof = {
//     subst.map.toList.head._2 match {
//        case IntZero() => CloneLKProof(schema.base)
//        case _ => apply(schema.rec, subst)
//     }
//  }


  //************************************************************************************
  def apply( proof_name: String, number: Int, trs: dbTRS ): LKProof = {
    if (number < 1) {
      println("\nproof_name = "+proof_name)
      println("number = "+number)

//      RemoveEqRulesFromGroundSchemaProof(SchemaProofDB.get(proof_name).base)
      SchemaProofDB.get(proof_name).base
    }
    else {
      println("\nproof_name = "+proof_name)
      println("number = "+number)
      val k = IntVar(new VariableStringSymbol("k")) ;
      val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, toIntegerTerm(number-1))
      val subst = new SchemaSubstitution1[HOLExpression](new_map)
//      RemoveEqRulesFromGroundSchemaProof(apply(SchemaProofDB.get(proof_name).rec, subst, number))
      apply(SchemaProofDB.get(proof_name).rec, subst, number, trs)
    }
  }

  def toIntegerTerm(i: Int): IntegerTerm = {
    if (i == 0)
      IntZero()
    else
      Succ(toIntegerTerm(i-1))
  }

  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] , cnt: Int, trs: dbTRS) : LKProof = {
//    println("\n"+proof.rule)
    println("cnt = "+cnt)

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
        println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
          val new_ind = subst(ind)

          //subst.map.toList.foreach(p => println(p._1,p._2))
          //subst.map.head._2 match {


          if (cnt == 0)
            CloneLKProof(SchemaProofDB.get(link).base)
      /*    new_ind match {
          case IntZero() => {
                    // val res = (CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
                    val res = CloneLKProof(SchemaProofDB.get(link).base)
     //               printSchemaProof(res._1)
                    res
          } */

          else
            if (cnt == 1) {

//                apply(SchemaProofDB.get(link), new_subst, cnt1)
              new_ind match {
                case y:IntZero => {
//                println("\nnew_ind = "+0)
                CloneLKProof(SchemaProofDB.get(link).base)
                }
                case _ => {
//                println("\nnew_ind > "+0)
                apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]), trs)
//                CloneLKProof(SchemaProofDB.get(link).base)
                }
              }
            }
            else {
              if(StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]) == cnt) {
                apply(SchemaProofDB.get(link).rec, subst, cnt, trs)
              }
              else {
                val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Pair(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
                val new_subst = new SchemaSubstitution1(new_map)
  //              val cnt1 = cnt - 1
                apply(SchemaProofDB.get(link).rec, new_subst, cnt-1, trs)
              }
            }

      //      }
 //           apply(SchemaProofDB.get(link), new_subst)

      }

      case AndEquivalenceRule1(up, r, aux, main) =>  {
    //    println("\n UnaryProof AndEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        val up1 = apply(up, subst, cnt, trs)
   //     println("\n"+proof.rule+")")
   //     println("\n aux = "+printSchemaProof.formulaToString(subst(aux.formula)))

   //     println("\nAndEquivalenceRule1 up1: "+printSchemaProof.sequentToString(up1.root))
        AndEquivalenceRule1(up1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
//        println("\n UnaryProof OrEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        OrEquivalenceRule1(apply(up, subst, cnt, trs), subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case Axiom(_) => {
        println("\n"+proof.rule)
        val res = handleRule( proof, Nil, subst, trs )
//        println("\nafter : "+res.rule)
        res
      }
      case UnaryLKProof(_, p, _, _, _) => {
        println("\n"+proof.rule)
        val res = handleRule( proof, apply( p, subst, cnt, trs )::Nil, subst, trs )
//        println("\nafter : "+res.rule)
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        println("\n"+proof.rule)
        val pr1 = apply( p1, subst, cnt, trs )
        val pr2 = apply( p2, subst, cnt, trs )
   //     println("\n"+proof.rule)
    //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
     //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
      //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
        val res = handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
//        println("\nafter : "+res.rule)
        res
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        println("\n"+proof.rule)
        val res = handleRule( proof, apply( p1, subst, cnt, trs )::apply( p2, subst, cnt, trs )::Nil, subst, trs )
//        println("\nafter : "+res.rule)
        res
      }
      case _ => {println("\n\n\nERROR in apply schema substitution\n"); proof}
    }
  }
}




