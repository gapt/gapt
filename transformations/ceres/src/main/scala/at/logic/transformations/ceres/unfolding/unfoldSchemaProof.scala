// --------------------- substitution begin

package at.logic.transformations.ceres.unfolding


import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema._
import at.logic.language.schema.IndexedPredicate._
import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import scala.xml._
import at.logic.calculi.slk._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
import at.logic.calculi.lksk.{Axiom => LKskAxiom,
WeakeningLeftRule => LKskWeakeningLeftRule,
WeakeningRightRule => LKskWeakeningRightRule,
ForallSkLeftRule, ForallSkRightRule, ExistsSkLeftRule, ExistsSkRightRule}

import  at.logic.transformations.ceres.projections.printSchemaProof
import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.{HOLFormula}
import scala.Predef._

//import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
//import at.logic.language.schema.SchemaSubstitution

object applySchemaSubstitution {
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
                        constructor: (LKProof, HOLFormula) => LKProof) = {
 //   println("n = "+subst.map.toList.head._2)
 //   println("handleContraction \n\n1"+printSchemaProof.sequentToString(new_parent._1.root))
 //   println("2\n\n"+printSchemaProof.formulaToString(subst(a1.formula)))

 //   println("3\n\n"+printSchemaProof.sequentToString(old_parent.root))
  //  println("4\n\n"+printSchemaProof.formulaToString(a1.formula))

//    println("4\n\n"+printSchemaProof.sequentToString(old_proof.root))


    constructor( new_parent, subst(a1.formula).asInstanceOf[HOLFormula] )
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



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: SchemaSubstitution1[HOLExpression] ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => {
        val a = Axiom(ro.antecedent.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]),ro.succedent.toList.map(fo => subst(fo.formula).asInstanceOf[HOLFormula]))
//        val ant_occs = a._1.root.antecedent.toList
//        val succ_occs = a._1.root.succedent.toList
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
//        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
//        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
        a
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionRightRule.apply )
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
//        println("Cut:")
//        println(printSchemaProof.sequentToString(new_p1.root))
//        println("aux = "+printSchemaProof.formulaToString(subst( a1.formula )))
//        println(printSchemaProof.sequentToString(new_p2.root))
        //val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        val new_proof = CutRule( new_p1, new_p2, subst( a1.formula ).asInstanceOf[HOLFormula] )
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
        val new_proof = AndLeft1Rule( new_parent, subst(a.formula).asInstanceOf[HOLFormula], subst( f ).asInstanceOf[HOLFormula] )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
//        val new_proof = AndLeft2Rule( new_parent._1, subst( f ).asInstanceOf[HOLFormula], new_parent._2( a ) )
        val new_proof = AndLeft2Rule( new_parent, subst( f ).asInstanceOf[HOLFormula], subst(a.formula).asInstanceOf[HOLFormula] )
        new_proof
      }
  //    case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = new_parents.head
//        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), subst( f ).asInstanceOf[HOLFormula] )
        val new_proof = OrRight1Rule( new_parent, subst( a.formula ).asInstanceOf[HOLFormula], subst( f ).asInstanceOf[HOLFormula] )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, subst( f ).asInstanceOf[HOLFormula], subst( a.formula ).asInstanceOf[HOLFormula] )
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


    }
  }

//  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : LKProof = {
//     subst.map.toList.head._2 match {
//        case IntZero() => CloneLKProof(schema.base)
//        case _ => apply(schema.rec, subst)
//     }
//  }


  //************************************************************************************
  def apply( proof_name: String, number: Int ): LKProof = {
    if (number < 1)
      RemoveEqRulesFromGroundSchemaProof(SchemaProofDB.get(proof_name).base)
    else {
      val k = IntVar(new VariableStringSymbol("k")) ;
      val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, toIntegerTerm(number-1))
      val subst = new SchemaSubstitution1[HOLExpression](new_map)
      RemoveEqRulesFromGroundSchemaProof(apply(SchemaProofDB.get(proof_name).rec, subst, number))
    }
  }

  def toIntegerTerm(i: Int): IntegerTerm = {
    if (i == 0)
      IntZero()
    else
      Succ(toIntegerTerm(i-1))
  }

  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] , cnt: Int) : LKProof = {
//    println("\n"+proof.rule)

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
     //   println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
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
                apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]))
//                CloneLKProof(SchemaProofDB.get(link).base)
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

      case Axiom(_) => {
        val res = handleRule( proof, Nil, subst )
    //    println("\nAxiom")
        res
       }
      case UnaryLKProof(_, p, _, _, _) => {
        val res = handleRule( proof, apply( p, subst, cnt )::Nil, subst )
  //      println("\n"+proof.rule+")")
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        val pr1 = apply( p1, subst, cnt )
        val pr2 = apply( p2, subst, cnt )
   //     println("\n"+proof.rule)
    //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
     //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
      //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
        handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        val res = handleRule( proof, apply( p1, subst, cnt )::apply( p2, subst, cnt )::Nil, subst )
  //      println("\n"+proof.rule)
        res
      }
      case _ => {println("\n\n\nERROR in apply schema substitution\n"); proof}
    }
  }
}




//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
object CloneLKProof {
import at.logic.language.hol._

    def apply(p: LKProof):LKProof = {
//      println("\nCloneLKProof : "+p.rule)
      p match {

        case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))

        case AndLeftEquivalenceRule1(p, s, a, m) => {
//            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
            val new_p = apply(p)
            AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndRightEquivalenceRule1(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule1\n")
            val new_p = apply(p)
            AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case OrRightEquivalenceRule1(p, s, a, m) => {
           // println("\nOrRightEquivalenceRule1\n")
            val new_p = apply(p)
            OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndLeftEquivalenceRule3(p, s, a, m) => {
           // println("\nAndLeftEquivalenceRule3\n")
            val new_p = apply(p)
            AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case AndRightEquivalenceRule3(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule3\n")
            val new_p = apply(p)
            AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case OrRightEquivalenceRule3(p, s, a, m) => {
          //println("\nOrRightEquivalenceRule3\n")
          val new_p = apply(p)
          OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
        }

        case WeakeningLeftRule(p, _, m) => {
            val new_p = apply(p)
            implicit val factory = defaultFormulaOccurrenceFactory
            WeakeningLeftRule( new_p, m.formula )
        }

        case WeakeningRightRule(p, _, m) => {
            val new_p = apply(p)
            implicit val factory = defaultFormulaOccurrenceFactory
            WeakeningRightRule( new_p, m.formula )
        }

        case CutRule( p1, p2, _, a1, a2 ) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            CutRule(new_p1, new_p2, a2.formula)
        }

        case OrLeftRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
        }

        case AndRightRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
        }

        case NegLeftRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegLeftRule( new_p, a.formula )
        }

        case AndLeft1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, right) => right }
      //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
       //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
            AndLeft1Rule( new_p, a.formula, a2)
        }

        case AndLeft2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, _) => l }
       //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
       //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
       //     println(printSchemaProof.formulaToString(a2))
            AndLeft2Rule( new_p, a2, a.formula )
        }

        case OrRight1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(_, r) => r }
//            println("\np or:r1 = "+p.root)
//            println("\nnew_p or:r1 = "+new_p.root)
//            println("\nor:r1 a = "+a.formula)
//            println("\nor:r1 m = "+m.formula)
            OrRight1Rule( new_p, a.formula, a2)
        }

        case OrRight2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(l, _) => l }
//            println("\np or:r2 = "+p.root)
//            println("\nnew_p or:r2 = "+new_p.root)
//          println("\nor:r2 a = "+a.formula)
//            println("\nor:r2 m = "+m.formula)
            OrRight2Rule( new_p, a2, a.formula)
        }

        case NegRightRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegRightRule( new_p, a.formula )
        }

        case ContractionLeftRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
            ContractionLeftRule( new_p, a1.formula )
        }

        case ContractionRightRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
//            println("\nc:r = "+new_p.root)
            ContractionRightRule( new_p, a1.formula )
        }
        case _ => { println("ERROR in CloneLKProof : missing rule!");throw new Exception("ERROR in unfolding: CloneLKProof") }
    }}
}


class SchemaSubstitution1[T <: HOLExpression](val map: scala.collection.immutable.Map[Var, T])  {
  import at.logic.language.schema._

  def apply(expression: T): T = expression match {
      case x:IntVar => {
          map.get(x) match {
            case Some(t) => {
              //println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case _ => {
              //println(x + " Error in schema subst 1")
              x.asInstanceOf[T]
            }
          }
      }
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]

      case _ => expression
    }

  def apply(fseq: types.FSequent): types.FSequent = {
    FSequent(fseq._1.map(f => apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]),fseq._2.map(f => apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]))
  }
}
//substitution end


object checkProofLinks1 {
    def apply(p: LKProof):Unit = p match {
      case Axiom(so) => {}
      case UnaryLKProof(_,upperProof,_,_,_) => checkProofLinks1( upperProof )
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) =>
        checkProofLinks1( upperProofLeft ); checkProofLinks1( upperProofRight )
      case UnarySchemaProof(_,upperProof,_,_,_) => checkProofLinks1( upperProof )
      case SchemaProofLinkRule(so, name, indices) => {
        val ps = SchemaProofDB.get( name )
        // FIXME: cast needed???
//        val sub = new SchemaSubstitution(ps.vars.zip(indices.asInstanceOf[List[HOLExpression]]))
        val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(ps.vars.head, indices.head)
        val sub = new SchemaSubstitution1[HOLExpression](new_map)
     //   require( substitute(sub, ps.seq) == so.getSequent, "Proof Link to proof " + name + "(" + indices + ") with sequent " + so.getSequent + " incorrect!")

//        require( ps.seq.antecedent.map(fo => fo.formula).toSet == so.antecedent.map(fo => sub(fo.formula)).toSet)
//        require( ps.seq.succedent.map(fo => fo.formula).toSet == so.succedent.map(fo => sub(fo.formula)).toSet)
//        if(ps.seq != substitute(sub , so.toFSequent()))

        if(sub(ps.seq)._1.toSet != so.toFSequent()._1.toSet || sub(ps.seq)._2.toSet != so.toFSequent()._2.toSet)
        {
          println("\n checkProofLinks1 for proof "+ name +" FAIL")
          ps.seq._1.foreach(f => println("\n"+f))
                    println("\n\n")
          sub(so.toFSequent())._1.foreach(f => println("\n"+f))

        }
        else
        {
          println("checkProofLinks1 for proof "+ name+" SUCCESS")
        }
//        require(ps.seq == substitute(sub , so.toFSequent()) )

      }

      case _ => throw new Exception("\nNo such rule in checkProofLinks1")
    }
}


object StepMinusOne {
import at.logic.language.hol._

    def intTermMinusOne(t: IntegerTerm, k:IntVar): IntegerTerm =  {
      if(length(t, k) > 0)
        Pred(t)
      else {
    //    println("WARNING : intTermMinusOne !")
        t
      }
    }

    def length(t: IntegerTerm, k:IntVar): Int = t match {
      case y: IntVar if y == k => 0
      case c: IntZero => 0
      case Succ(t1) => {
        1 + length(t1, k)
      }
      case _ => -10000
    }

    def lengthGround(t: IntegerTerm): Int = t match {
      case c: IntZero => 0
      case Succ(t1) => {
        1 + lengthGround(t1)
      }
      case _ => throw new Exception("lengthGround")
    }

    def lengthVar(t: IntegerTerm): Int = t match {
      case y: IntVar => 0
      case Succ(t1) => {
        1 + lengthVar(t1)
      }
      case _ => throw new Exception("lengthVar")
    }


    //return an axpression such that all s(k) is substituted by k
    def minusOne(e: HOLExpression, k:IntVar): HOLExpression = e match {
      case x:IntegerTerm => intTermMinusOne(x, k)
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], minusOne(l.head.asInstanceOf[HOLExpression], k).asInstanceOf[IntegerTerm])
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, minusOne(init.asInstanceOf[IntegerTerm], k).asInstanceOf[IntegerTerm], minusOne(end.asInstanceOf[IntegerTerm], k).asInstanceOf[IntegerTerm] ).asInstanceOf[HOLFormula]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, minusOne(init.asInstanceOf[IntegerTerm], k).asInstanceOf[IntegerTerm], minusOne(end.asInstanceOf[IntegerTerm], k).asInstanceOf[IntegerTerm] ).asInstanceOf[HOLFormula]
      case Or(l @ left, r @ right) => Or(minusOne(l.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula], minusOne(r.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]
      case And(l @ left, r @ right) => And(minusOne(l.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula], minusOne(r.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula]
      case Neg(l @ left) => Neg(minusOne(l.asInstanceOf[HOLFormula], k).asInstanceOf[SchemaFormula]).asInstanceOf[HOLFormula]

      case _ => e
    }

    def minusMore(e: HOLExpression, k:IntVar, times: Int): HOLExpression = {
      if (times == 0)
        e
      else
        minusMore(minusOne(e, k), k, times-1)
    }

    def minusOneFSeq(fseq: types.FSequent, k:IntVar): types.FSequent = {
      FSequent(fseq._1.map(f => minusOne(f, k).asInstanceOf[HOLFormula]),fseq._2.map(f => minusOne(f, k).asInstanceOf[HOLFormula]))
    }

    def intTermPlus(t: IntegerTerm, times: Int): IntegerTerm = {
      if (times == 0)
        t
      else {
        intTermPlus(Succ(t), times-1)
      }
    }


//----------------------


  def apply(p: LKProof, k:IntVar):LKProof = {
    println("\nStepMinusOne : "+p.rule)
    p match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => minusOne(fo.formula.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula]),ro.succedent.map(fo => minusOne(fo.formula.asInstanceOf[HOLFormula], k).asInstanceOf[HOLFormula]))

      case SchemaProofLinkRule( seq, link, ind::_ ) => {
        SchemaProofLinkRule(minusOneFSeq(seq.toFSequent, k), link, intTermMinusOne(ind, k)::Nil )
      }

      case AndLeftEquivalenceRule1(p, s, a, m) => {
//            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
          val new_p = apply(p, k)
          AndLeftEquivalenceRule1(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
         // println("\nAndRightEquivalenceRule1\n")
          val new_p = apply(p, k)
          AndRightEquivalenceRule1(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
         // println("\nOrRightEquivalenceRule1\n")
          val new_p = apply(p, k)
          OrRightEquivalenceRule1(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
         // println("\nAndLeftEquivalenceRule3\n")
          val new_p = apply(p, k)
          AndLeftEquivalenceRule3(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
         // println("\nAndRightEquivalenceRule3\n")
          val new_p = apply(p, k)
          AndRightEquivalenceRule3(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        //println("\nOrRightEquivalenceRule3\n")
        val new_p = apply(p, k)
        OrRightEquivalenceRule3(new_p, minusOne(a.formula, k).asInstanceOf[SchemaFormula], minusOne(m.formula, k).asInstanceOf[SchemaFormula])
      }

      case WeakeningLeftRule(p, _, m) => {
          val new_p = apply(p, k)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningLeftRule( new_p, minusOne(m.formula, k).asInstanceOf[HOLFormula] )
      }

      case WeakeningRightRule(p, _, m) => {
          val new_p = apply(p, k)
          implicit val factory = defaultFormulaOccurrenceFactory
          WeakeningRightRule( new_p, minusOne(m.formula, k).asInstanceOf[HOLFormula] )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          CutRule(new_p1, new_p2, minusOne(a2.formula, k).asInstanceOf[HOLFormula])
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          OrLeftRule(new_p1, new_p2, minusOne(a1.formula, k).asInstanceOf[HOLFormula], minusOne(a2.formula, k).asInstanceOf[HOLFormula])
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          AndRightRule(new_p1, new_p2, minusOne(a1.formula, k).asInstanceOf[HOLFormula], minusOne(a2.formula, k).asInstanceOf[HOLFormula])
      }

      case NegLeftRule( p, _, a, m ) => {
          val new_p = apply(p, k)
          NegLeftRule( new_p, minusOne(a.formula, k).asInstanceOf[HOLFormula] )
      }

      case AndLeft1Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case And(l, right) => right }
    //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
     //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
      //    println(printSchemaProof.formulaToString(a2))
          AndLeft1Rule( new_p, minusOne(a.formula, k).asInstanceOf[HOLFormula], minusOne(a2, k).asInstanceOf[HOLFormula])
      }

      case AndLeft2Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case And(l, _) => l }
     //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
     //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
     //     println(printSchemaProof.formulaToString(a2))
          AndLeft2Rule( new_p, minusOne(a2, k).asInstanceOf[HOLFormula], minusOne(a.formula, k).asInstanceOf[HOLFormula] )
      }

      case OrRight1Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case Or(_, r) => r }
//            println("\np or:r1 = "+p.root)
//            println("\nnew_p or:r1 = "+new_p.root)
//            println("\nor:r1 a = "+a.formula)
//            println("\nor:r1 m = "+m.formula)
          OrRight1Rule( new_p, minusOne(a.formula, k).asInstanceOf[HOLFormula], minusOne(a2, k).asInstanceOf[HOLFormula])
      }

      case OrRight2Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case Or(l, _) => l }
//            println("\np or:r2 = "+p.root)
//            println("\nnew_p or:r2 = "+new_p.root)
//          println("\nor:r2 a = "+a.formula)
//            println("\nor:r2 m = "+m.formula)
          OrRight2Rule( new_p, minusOne(a2, k).asInstanceOf[HOLFormula], minusOne(a.formula, k).asInstanceOf[HOLFormula])
      }

      case NegRightRule( p, _, a, m ) => {
          val new_p = apply(p, k)
          NegRightRule( new_p, minusOne(a.formula, k).asInstanceOf[HOLFormula] )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
          val new_p = apply(p, k)
          ContractionLeftRule( new_p, minusOne(a1.formula, k).asInstanceOf[HOLFormula] )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
          val new_p = apply(p, k)
//            println("\nc:r = "+new_p.root)
          ContractionRightRule( new_p, minusOne(a1.formula, k).asInstanceOf[HOLFormula] )
      }
      case _ => { println("ERROR in StepMinusOne : missing rule!");throw new Exception("ERROR in unfolding: StepMinusOne") }
    }
  }
}


//unfold the ground BigAnd/BigOr skipping all equivalence inferences
object RemoveEqRulesFromGroundSchemaProof {
import at.logic.language.hol._

    def apply(p: LKProof):LKProof = {
      p match {

        case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))

        case AndLeftEquivalenceRule1(p, s, a, m) => {
//            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
//            val new_p = apply(p)
//            AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
              apply(p)
        }

        case AndRightEquivalenceRule1(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule1\n")
//            val new_p = apply(p)
//            AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
            apply(p)
        }

        case OrRightEquivalenceRule1(p, s, a, m) => {
           // println("\nOrRightEquivalenceRule1\n")
//            val new_p = apply(p)
//            OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
          apply(p)
        }

        case AndLeftEquivalenceRule3(p, s, a, m) => {
           // println("\nAndLeftEquivalenceRule3\n")
//            val new_p = apply(p)
//            AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
          apply(p)
        }

        case AndRightEquivalenceRule3(p, s, a, m) => {
           // println("\nAndRightEquivalenceRule3\n")
//            val new_p = apply(p)
//            AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
          apply(p)
        }

        case OrRightEquivalenceRule3(p, s, a, m) => {
          //println("\nOrRightEquivalenceRule3\n")
//          val new_p = apply(p)
//          OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
          apply(p)
        }

        case WeakeningLeftRule(p, _, m) => {
            val new_p = apply(p)
            implicit val factory = defaultFormulaOccurrenceFactory
            WeakeningLeftRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(m.formula ))
        }

        case WeakeningRightRule(p, _, m) => {
            val new_p = apply(p)
            implicit val factory = defaultFormulaOccurrenceFactory
            WeakeningRightRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(m.formula ))
        }

        case CutRule( p1, p2, _, a1, a2 ) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            CutRule(new_p1, new_p2, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2.formula))
        }

        case OrLeftRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            OrLeftRule(new_p1, new_p2, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a1.formula), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2.formula))
        }

        case AndRightRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            AndRightRule(new_p1, new_p2, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a1.formula), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2.formula) )
        }

        case NegLeftRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegLeftRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula ))
        }

        case AndLeft1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, right) => right }
//            println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
//            println("aux : \n"+printSchemaProof.formulaToString(a.formula))
//            println(printSchemaProof.formulaToString(a2))
            AndLeft1Rule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2))
        }

        case AndLeft2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, _) => l }
       //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
       //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
       //     println(printSchemaProof.formulaToString(a2))
            AndLeft2Rule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula) )
        }

        case OrRight1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(_, r) => r }
//            println("\np or:r1 = "+p.root)
//            println("\nnew_p or:r1 = "+new_p.root)
//            println("\nor:r1 a = "+a.formula)
//            println("\nor:r1 m = "+m.formula)
            OrRight1Rule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2))
        }

        case OrRight2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(l, _) => l }
//            println("\np or:r2 = "+p.root)
//            println("\nnew_p or:r2 = "+new_p.root)
//          println("\nor:r2 a = "+a.formula)
//            println("\nor:r2 m = "+m.formula)
            OrRight2Rule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a2), RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula))
        }

        case NegRightRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegRightRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a.formula ))
        }

        case ContractionLeftRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
//            println("c:l -> "+printSchemaProof.sequentToString(new_p.root))
//            println("aux1 : \n"+printSchemaProof.formulaToString(a1.formula))
//            println("aux2 : \n"+printSchemaProof.formulaToString(a2.formula))
            ContractionLeftRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a1.formula ))
        }

        case ContractionRightRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
//            println("\nc:r = "+new_p.root)
            ContractionRightRule( new_p, RemoveEqRulesFromGroundSchemaProof.unfoldGroundSchF(a1.formula ))
        }
        case _ => { println("ERROR in object RemoveEqRulesFromGroundSchemaProof : missing rule!");throw new Exception("ERROR in unfolding: object RemoveEqRulesFromGroundSchemaProof") }
      }
    }


    // BigAnd(1,3,A_i) => A_1 /\ A_2 /\ A_3. Now works for 1 index, soon it will work for many
    def unfoldGroundSchF(f: HOLFormula): HOLFormula = f match {
      case BigAnd(v, formula, init, end) =>
        andNSchemaF(formula, StepMinusOne.lengthGround(init), StepMinusOne.lengthGround(end))
//      case BigOr(v, formula, init, end) =>
//        orNSchemaF(formula, StepMinusOne.lengthGround(init), StepMinusOne.lengthGround(end))
      case And(l @ left, r @ right) => And(unfoldGroundSchF(l), unfoldGroundSchF(r))
      case Or(l @ left, r @ right) => Or(unfoldGroundSchF(l), unfoldGroundSchF(r))
      case Neg(l @ left) => Neg(unfoldGroundSchF(l))
      case _ => f
    }

    def groundSchemaF(f: HOLFormula, init: Int): HOLFormula = f match {
      case IndexedPredicate(pointer @ f1, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], applySchemaSubstitution.toIntegerTerm(init+StepMinusOne.lengthVar(l.head.asInstanceOf[IntegerTerm])))
      case And(l @ left, r @ right) => And(groundSchemaF(l, init), groundSchemaF(r, init))
      case Or(l @ left, r @ right) => Or(groundSchemaF(l, init), groundSchemaF(r, init))
      case Neg(l @ left) => Neg(groundSchemaF(l, init))
      case _ => throw new Exception("groundSchemaF")
    }

    // apply N-times And on a grounded f
    def andNSchemaF(f: HOLFormula, init: Int, end: Int): HOLFormula = {
      if (init == end)
        groundSchemaF(f, init)
      else {
        def list = (init to end).toList
        val l1 = list.map(i =>  {
          f match {
            case IndexedPredicate(pointer @ f1, l @ ts) => groundSchemaF(f, i)
            case And(l @ left, r @ right) => And(groundSchemaF(l, i), groundSchemaF(r, i))
            case Or(l @ left, r @ right) => Or(groundSchemaF(l, i), groundSchemaF(r, i))
            case Neg(l @ left) => Neg(groundSchemaF(l, i))
            case _ => throw new Exception("andNSchemaF")
          }
        })
        l1.tail.foldLeft(l1.head)((x, res) => And(x, res))
      }
    }


    // apply N-times And on a grounded f
//    def orNSchemaF(f: HOLFormula, init: Int, end: Int): HOLFormula = {
//      if (init == end)
//        groundSchemaF(f, init)
//      else
//        for (i<-init to end ) {
//          f match {
//            case IndexedPredicate(pointer @ f1, l @ ts) => Or(groundSchemaF(f, i), andNSchemaF(f, i+1, end))
//            case And(l @ left, r @ right) => Or(And(groundSchemaF(l, i), groundSchemaF(r, i)) , andNSchemaF(f, init+1, end))
//            case Or(l @ left, r @ right) => Or(Or(groundSchemaF(l, i), groundSchemaF(r, i)) , andNSchemaF(f, init+1, end))
//            case Neg(l @ left) => Or(Neg(groundSchemaF(l, i)) , andNSchemaF(f, init+1, end))
//            case _ => throw new Exception("andNSchemaF")
//          }
//        }
//    }

}