// --------------------- substitution begin

package at.logic.transformations.ceres.unfolding


import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import scala.xml._
import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr}
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
//import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.schema._
import at.logic.language.schema.IntegerTerm
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

  def apply(schema : SchemaProof, subst: SchemaSubstitution1[HOLExpression]) : LKProof = {
     subst.map.toList.head._2 match {
        case IntZero() => CloneLKProof(schema.base)
        case _ => apply(schema.rec, subst)
     }
  }

  def apply( proof: LKProof, subst: SchemaSubstitution1[HOLExpression] ) : LKProof = {
 //   println("\n"+proof.rule+")")

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
     //   println("\nSchemaProofLinkRule for proof "+link+" , "+ind)
          val new_ind = subst(ind)
          val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Pair(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
          val new_subst = new SchemaSubstitution1(new_map)

          //subst.map.toList.foreach(p => println(p._1,p._2))
          //subst.map.head._2 match {

          new_ind match {
          case IntZero() => {
                    // val res = (CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
                    val res = CloneLKProof(SchemaProofDB.get(link).base)
     //               printSchemaProof(res._1)
                    res
          }

          case _ => {
      //      val varmap = subst.map.head._1.asInstanceOf[Var]
       //     val new_map1 = (subst.map - varmap) + Pair(varmap, Pred(subst.map.head._2.asInstanceOf[IntegerTerm]))
       //     val new_subst = new SchemaSubstitution1(new_map1)
  //          new_subst.map.toList.head._2 match {
    //            case IntZero() =>  Pair(CloneLKProof(SchemaProofDB.get(link).base), new HashMap[FormulaOccurrence, FormulaOccurrence])
         //       case _ =>
                    apply(SchemaProofDB.get(link), new_subst)
      //      }
 //           apply(SchemaProofDB.get(link), new_subst)
          }
        }
      }
      case AndEquivalenceRule1(up, r, aux, main) =>  {
    //    println("\n UnaryProof AndEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        val up1 = apply(up, subst)
   //     println("\n"+proof.rule+")")
   //     println("\n aux = "+printSchemaProof.formulaToString(subst(aux.formula)))

   //     println("\nAndEquivalenceRule1 up1: "+printSchemaProof.sequentToString(up1.root))
        AndEquivalenceRule1(up1, subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
//        println("\n UnaryProof OrEquivalenceRule1: "+printSchemaProof.sequentToString(r))
        OrEquivalenceRule1(apply(up, subst), subst(aux.formula).asInstanceOf[SchemaFormula], subst(main.formula).asInstanceOf[SchemaFormula])
      }

      case Axiom(_) => {
        val res = handleRule( proof, Nil, subst )
    //    println("\nAxiom")
        res
       }
      case UnaryLKProof(_, p, _, _, _) => {
        val res = handleRule( proof, apply( p, subst )::Nil, subst )
  //      println("\n"+proof.rule+")")
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        val pr1 = apply( p1, subst )
        val pr2 = apply( p2, subst )
   //     println("\n"+proof.rule)
    //    println("\nleft  proof seq:"+printSchemaProof.sequentToString(pr1._1.root))
     //   println("\nright proof seq:"+printSchemaProof.sequentToString(pr2._1.root))
      //  println("\naux f :"+printSchemaProof.formulaToString(subst(a1.formula))+"     |     "+printSchemaProof.formulaToString(subst(a2.formula)))
        handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        val res = handleRule( proof, apply( p1, subst )::apply( p2, subst )::Nil, subst )
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
      println("\nCloneLKProof : "+p.rule)
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

        case NegRightRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegRightRule( new_p, a.formula )
        }

        case ContractionLeftRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
            ContractionLeftRule( new_p, a1.formula )
        }
        case _ => { println("ERROR in CloneLKProof !");throw new Exception("ERROR in unfolding: CloneLKProof") }
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
}
//substitution end
