// --------------------- substitution begin

package at.logic.algorithms.shlk

import at.logic.language.schema._
import at.logic.calculi.occurrences._
import at.logic.calculi.slk._
import at.logic.calculi.lksk.{Axiom => _, WeakeningLeftRule => _, WeakeningRightRule => _, _}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.{UnfoldException, CloneLKProof}

//import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}

object applySchemaSubstitution {
  def handleSchemaEquivalenceRule ( new_parent: LKProof,
                                    subst: Substitution,
                                    old_parent: LKProof,
                                    old_proof: LKProof,
                                    constructor: (LKProof, SchemaFormula) => LKProof with PrincipalFormulas,
                                    m: FormulaOccurrence
                                    ) = {
      val new_proof = constructor( new_parent, subst(m.formula.asInstanceOf[SchemaFormula]))
      new_proof
  }




  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
  def handleWeakening( new_parent: LKProof,
                       subst: Substitution,
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, SchemaFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
     val new_proof = constructor( new_parent, subst(m.formula.asInstanceOf[SchemaFormula]) )
     new_proof
  }
  def handleContraction( new_parent: LKProof,
                         subst: Substitution,
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                        constructor: (LKProof, SchemaFormula) => LKProof) = {


    constructor( new_parent, subst(a1.formula.asInstanceOf[SchemaFormula]) )
  }
  def handleBinaryProp( new_parent_1: LKProof,
                        new_parent_2: LKProof,
                        subst: Substitution,
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, SchemaFormula, SchemaFormula) => LKProof) = {

     constructor( new_parent_1, new_parent_2, subst(a1.formula.asInstanceOf[SchemaFormula]), subst(a2.formula.asInstanceOf[SchemaFormula]) )
  }



  def handleRule( proof: LKProof, new_parents: List[LKProof], subst: Substitution ) : LKProof = {
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => subst(fo.formula.asInstanceOf[SchemaFormula])),ro.succedent.toList.map(fo => subst(fo.formula.asInstanceOf[SchemaFormula])))
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, subst, p, proof, a1, a2, ContractionRightRule.apply )
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        val new_proof = CutRule( new_p1, new_p2, subst(a1.formula.asInstanceOf[SchemaFormula]) )
        new_proof
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, subst, a1, a2, p1, p2, proof, AndRightRule.apply )

      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft1Rule( new_parent, subst(a.formula.asInstanceOf[SchemaFormula]), subst(f) )
        new_proof
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft2Rule( new_parent, subst(f), subst(a.formula.asInstanceOf[SchemaFormula]) )
        new_proof
      }

      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight1Rule( new_parent, subst(a.formula.asInstanceOf[SchemaFormula]), subst(f) )
        new_proof
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent, subst(f), subst(a.formula.asInstanceOf[SchemaFormula]) )
        new_proof
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegLeftRule( new_parent, subst(a.formula.asInstanceOf[SchemaFormula]) )
        new_proof
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegRightRule( new_parent, subst(a.formula.asInstanceOf[SchemaFormula]) )
        new_proof
      }


    }
  }

  //************************************************************************************
  def apply( proof_name: String, number: Int ): LKProof = {
    if (number < 1)
      RemoveEqRulesFromGroundSchemaProof(SchemaProofDB.get(proof_name).base)
    else {
      val k = IntVar("k")
      val subst = Substitution((k.asInstanceOf[SchemaVar], toIntegerTerm(number-1))::Nil)
      RemoveEqRulesFromGroundSchemaProof(apply(SchemaProofDB.get(proof_name).rec, subst, number))
    }
  }

  def apply( proof: LKProof, subst: Substitution , cnt: Int) : LKProof = {

    proof match {
      case SchemaProofLinkRule( seq, link, ind::_ ) => {
          val new_ind = subst(ind)
          if (cnt == 0)
            CloneLKProof(SchemaProofDB.get(link).base)
          else
            if (cnt == 1) {
              new_ind match {
                case y:IntZero => {
                CloneLKProof(SchemaProofDB.get(link).base)
                }
                case _ => {
                apply(SchemaProofDB.get(link).rec, subst, StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]))
                }
              }
            }
            else {
              if(StepMinusOne.length(new_ind.asInstanceOf[IntegerTerm], subst.map.head._1.asInstanceOf[IntVar]) == cnt) {
                apply(SchemaProofDB.get(link).rec, subst, cnt)
              }
              else {
                val new_map = (subst.schemamap - subst.schemamap.head._1) + Tuple2(subst.schemamap.head._1, Pred(new_ind.asInstanceOf[IntegerTerm]) )
                val new_subst = Substitution(new_map)
                apply(SchemaProofDB.get(link).rec, new_subst, cnt-1)
              }

            }
      }

      case AndEquivalenceRule1(up, r, aux, main) =>  {
        val up1 = apply(up, subst, cnt)
        AndEquivalenceRule1(up1, subst(aux.formula.asInstanceOf[SchemaFormula]), subst(main.formula.asInstanceOf[SchemaFormula]))
      }

      case OrEquivalenceRule1(up, r, aux, main) =>  {
        OrEquivalenceRule1(apply(up, subst, cnt), subst(aux.formula.asInstanceOf[SchemaFormula]), subst(main.formula.asInstanceOf[SchemaFormula]))
      }

      case Axiom(_) => {
        val res = handleRule( proof, Nil, subst )
        res
       }
      case UnaryLKProof(_, p, _, _, _) => {
        val res = handleRule( proof, apply( p, subst, cnt )::Nil, subst )
        res
      }

      case OrLeftRule(p1, p2, s, a1, a2, m) => {
        val pr1 = apply( p1, subst, cnt )
        val pr2 = apply( p2, subst, cnt )
        handleBinaryProp( pr1, pr2, subst, a1, a2, p1, p2, proof, OrLeftRule.apply )
      }

      case BinaryLKProof(_, p1, p2, _, _, _, _) => {
        val res = handleRule( proof, apply( p1, subst, cnt )::apply( p2, subst, cnt )::Nil, subst )
        res
      }
      case _ => {println("\n\n\nERROR in apply schema substitution\n"); proof}
    }
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
        val sub = Substitution((ps.vars.head, indices.head)::Nil)
        // Apply substitution to the whole sequent
        val sub_ant = ps.seq.antecedent.map(f => sub(f.asInstanceOf[SchemaFormula]))
        val sub_suc = ps.seq.succedent.map(f => sub(f.asInstanceOf[SchemaFormula]))

        if(sub_ant.toSet != so.toFSequent._1.toSet || sub_suc.toSet != so.toFSequent._2.toSet)
        {
          println("\n checkProofLinks1 for proof "+ name +" FAIL")
          ps.seq._1.foreach(f => println("\n"+f))
                    println("\n\n")
          val ant = so.toFSequent.antecedent.map(f => sub(f.asInstanceOf[SchemaFormula]))
          ant.foreach(f => println("\n"+f))
        }
        else
        {
          println("checkProofLinks1 for proof "+ name+" SUCCESS")
        }
      }

      case _ => throw new Exception("\nNo such rule in checkProofLinks1")
    }
}


object StepMinusOne {

    def intTermMinusOne(t: IntegerTerm, k:IntVar): IntegerTerm =  {
      if(length(t, k) > 0)
        Pred(t)
      else {
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
    def minusOne(e: SchemaExpression, k:IntVar): SchemaExpression = e match {
      case x:IntegerTerm => intTermMinusOne(x, k)
      case IndexedPredicate(pointer, l) => IndexedPredicate(pointer.name, minusOne(l.head, k).asInstanceOf[IntegerTerm])
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, minusOne(init, k).asInstanceOf[IntegerTerm], minusOne(end, k).asInstanceOf[IntegerTerm] )
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, minusOne(init, k).asInstanceOf[IntegerTerm], minusOne(end, k).asInstanceOf[IntegerTerm] )
      case Or(l, r) => Or(minusOne(l, k).asInstanceOf[SchemaFormula], minusOne(r, k).asInstanceOf[SchemaFormula])
      case And(l, r) => And(minusOne(l, k).asInstanceOf[SchemaFormula], minusOne(r, k).asInstanceOf[SchemaFormula])
      case Neg(l) => Neg(minusOne(l, k).asInstanceOf[SchemaFormula])
      case Imp(l, r) => Imp(minusOne(l, k).asInstanceOf[SchemaFormula], minusOne(r, k).asInstanceOf[SchemaFormula])
      case AllVar(v, f) => AllVar(v, minusOne(f, k).asInstanceOf[SchemaFormula])
      case Atom(name:SchemaVar, args) => Atom(name, args.map(x => minusOne(x, k)))
      case Atom(name:SchemaConst, args) => Atom(name, args.map(x => minusOne(x, k)))
      case ifo: indexedFOVar => indexedFOVar(ifo.name, minusOne(ifo.index, k).asInstanceOf[IntegerTerm])
      case indexedOmegaVar(name, index) => indexedOmegaVar(name, minusOne(index, k).asInstanceOf[IntegerTerm])
      case sTerm(name, i, args) => {
        sTerm(name, minusOne(i, k), args)
      }
      case foTerm(v, arg) => foTerm(v, minusOne(arg, k)::Nil)
      case _ => e
    }

    // Overloading to avoid all the castings
    def minusOne(f: SchemaFormula, k: IntVar) : SchemaFormula = minusOne(f.asInstanceOf[SchemaExpression], k).asInstanceOf[SchemaFormula]

    def minusMore(e: SchemaExpression, k:IntVar, times: Int): SchemaExpression = {
      if (times == 0)
        e
      else
        minusMore(minusOne(e, k), k, times-1)
    }

    def minusOneFSeq(fseq: FSequent, k:IntVar): FSequent = {
      FSequent(fseq._1.map(f => minusOne(f.asInstanceOf[SchemaFormula], k)),fseq._2.map(f => minusOne(f.asInstanceOf[SchemaFormula], k)))
    }

    def intTermPlus(t: IntegerTerm, times: Int): IntegerTerm = {
      if (times == 0)
        t
      else {
        intTermPlus(Succ(t), times-1)
      }
    }

  def indVarPlusIndConst(v: IntVar, c: IntegerTerm): IntegerTerm = c match {
    case IntZero() => v
    case Succ(i) => Succ(indVarPlusIndConst(v, i))
    case _ => throw new Exception(c.toString + " is not a constant!")
  }


//----------------------


  def apply(p: LKProof, k:IntVar):LKProof = {
    println("\nStepMinusOne : "+p.rule)
    p match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => minusOne(fo.formula.asInstanceOf[SchemaFormula], k)),ro.succedent.map(fo => minusOne(fo.formula.asInstanceOf[SchemaFormula], k)))

      case SchemaProofLinkRule( seq, link, ind::_ ) => {
        SchemaProofLinkRule(minusOneFSeq(seq.toFSequent, k), link, intTermMinusOne(ind.asInstanceOf[IntegerTerm], k)::Nil )
      }

      case AndLeftEquivalenceRule1(p, s, a, m) => {
          val new_p = apply(p, k)
          AndLeftEquivalenceRule1(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
          val new_p = apply(p, k)
          AndRightEquivalenceRule1(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
          val new_p = apply(p, k)
          OrRightEquivalenceRule1(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
          val new_p = apply(p, k)
          AndLeftEquivalenceRule3(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
          val new_p = apply(p, k)
          AndRightEquivalenceRule3(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p, k)
        OrRightEquivalenceRule3(new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(m.formula.asInstanceOf[SchemaFormula], k))
      }

      case WeakeningLeftRule(p, _, m) => {
          val new_p = apply(p, k)
          WeakeningLeftRule( new_p, minusOne(m.formula.asInstanceOf[SchemaFormula], k) )
      }

      case WeakeningRightRule(p, _, m) => {
          val new_p = apply(p, k)
          WeakeningRightRule( new_p, minusOne(m.formula.asInstanceOf[SchemaFormula], k) )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          CutRule(new_p1, new_p2, minusOne(a2.formula.asInstanceOf[SchemaFormula], k))
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          OrLeftRule(new_p1, new_p2, minusOne(a1.formula.asInstanceOf[SchemaFormula], k), minusOne(a2.formula.asInstanceOf[SchemaFormula], k))
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
          val new_p1 = apply(p1, k)
          val new_p2 = apply(p2, k)
          AndRightRule(new_p1, new_p2, minusOne(a1.formula.asInstanceOf[SchemaFormula], k), minusOne(a2.formula.asInstanceOf[SchemaFormula], k))
      }

      case NegLeftRule( p, _, a, m ) => {
          val new_p = apply(p, k)
          NegLeftRule( new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k) )
      }

      case AndLeft1Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case And(l, right) => right }
          AndLeft1Rule( new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(a2, k))
      }

      case AndLeft2Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case And(l, _) => l }
          AndLeft2Rule( new_p, minusOne(a2, k), minusOne(a.formula.asInstanceOf[SchemaFormula], k) )
      }

      case OrRight1Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case Or(_, r) => r }
          OrRight1Rule( new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k), minusOne(a2, k))
      }

      case OrRight2Rule(p, r, a, m) =>  {
          val new_p = apply(p, k)
          val a2 = m.formula  match { case Or(l, _) => l }
          OrRight2Rule( new_p, minusOne(a2, k), minusOne(a.formula.asInstanceOf[SchemaFormula], k))
      }

      case NegRightRule( p, _, a, m ) => {
          val new_p = apply(p, k)
          NegRightRule( new_p, minusOne(a.formula.asInstanceOf[SchemaFormula], k) )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
          val new_p = apply(p, k)
          ContractionLeftRule( new_p, minusOne(a1.formula.asInstanceOf[SchemaFormula], k) )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
          val new_p = apply(p, k)
          ContractionRightRule( new_p, minusOne(a1.formula.asInstanceOf[SchemaFormula], k) )
      }
      case _ => println("ERROR in StepMinusOne : missing rule!");throw new UnfoldException("ERROR in unfolding: StepMinusOne")
    }
  }
}


//unfold the ground BigAnd/BigOr skipping all equivalence inferences
object RemoveEqRulesFromGroundSchemaProof {

    def apply(p: LKProof):LKProof = {
      p match {

        case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[SchemaFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[SchemaFormula]))

        case AndLeftEquivalenceRule1(p, s, a, m) => apply(p)
        case AndRightEquivalenceRule1(p, s, a, m) => apply(p)
        case OrRightEquivalenceRule1(p, s, a, m) => apply(p)
        case AndLeftEquivalenceRule3(p, s, a, m) => apply(p)
        case AndRightEquivalenceRule3(p, s, a, m) => apply(p)
        case OrRightEquivalenceRule3(p, s, a, m) => apply(p)
        case WeakeningLeftRule(p, _, m) => {
            val new_p = apply(p)
            WeakeningLeftRule( new_p, unfoldGroundSchF(m.formula.asInstanceOf[SchemaFormula]))
        }

        case WeakeningRightRule(p, _, m) => {
            val new_p = apply(p)
            WeakeningRightRule( new_p, unfoldGroundSchF(m.formula.asInstanceOf[SchemaFormula] ))
        }

        case CutRule( p1, p2, _, a1, a2 ) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            CutRule(new_p1, new_p2, unfoldGroundSchF(a2.formula.asInstanceOf[SchemaFormula]))
        }

        case OrLeftRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            OrLeftRule(new_p1, new_p2, unfoldGroundSchF(a1.formula.asInstanceOf[SchemaFormula]), unfoldGroundSchF(a2.formula.asInstanceOf[SchemaFormula]))
        }

        case AndRightRule(p1, p2, _, a1, a2, m) => {
            val new_p1 = apply(p1)
            val new_p2 = apply(p2)
            AndRightRule(new_p1, new_p2, unfoldGroundSchF(a1.formula.asInstanceOf[SchemaFormula]), unfoldGroundSchF(a2.formula.asInstanceOf[SchemaFormula]) )
        }

        case NegLeftRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegLeftRule( new_p, unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula] ))
        }

        case AndLeft1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, right) => right }
            AndLeft1Rule( new_p, unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula]), unfoldGroundSchF(a2))
        }

        case AndLeft2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case And(l, _) => l }
            AndLeft2Rule( new_p, unfoldGroundSchF(a2), unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula]) )
        }

        case OrRight1Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(_, r) => r }
            OrRight1Rule( new_p, unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula]), unfoldGroundSchF(a2))
        }

        case OrRight2Rule(p, r, a, m) =>  {
            val new_p = apply(p)
            val a2 = m.formula  match { case Or(l, _) => l }
            OrRight2Rule( new_p, unfoldGroundSchF(a2), unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula]))
        }

        case NegRightRule( p, _, a, m ) => {
            val new_p = apply(p)
            NegRightRule( new_p, unfoldGroundSchF(a.formula.asInstanceOf[SchemaFormula] ))
        }

        case ContractionLeftRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
            ContractionLeftRule( new_p, unfoldGroundSchF(a1.formula.asInstanceOf[SchemaFormula] ))
        }

        case ContractionRightRule(p, _, a1, a2, m) => {
            val new_p = apply(p)
            ContractionRightRule( new_p, unfoldGroundSchF(a1.formula.asInstanceOf[SchemaFormula] ))
        }
        case _ => throw new UnfoldException("ERROR in unfolding: object RemoveEqRulesFromGroundSchemaProof")
      }
    }


    // BigAnd(1,3,A_i) => A_1 /\ A_2 /\ A_3. Now works for 1 index, soon it will work for many
    def unfoldGroundSchF(f: SchemaFormula): SchemaFormula = f match {
      case BigAnd(v, formula, init, end) =>
        andNSchemaF(formula, StepMinusOne.lengthGround(init), StepMinusOne.lengthGround(end))
      case And(l @ left, r @ right) => And(unfoldGroundSchF(l), unfoldGroundSchF(r))
      case Or(l @ left, r @ right) => Or(unfoldGroundSchF(l), unfoldGroundSchF(r))
      case Neg(l @ left) => Neg(unfoldGroundSchF(l))
      case _ => f
    }

    def groundSchemaF(f: SchemaFormula, init: Int): SchemaFormula = f match {
      case IndexedPredicate(pointer, l) => IndexedPredicate(pointer.name, toIntegerTerm(init+StepMinusOne.lengthVar(l.head.asInstanceOf[IntegerTerm])).asInstanceOf[IntegerTerm])
      case And(l, r) => And(groundSchemaF(l, init), groundSchemaF(r, init))
      case Or(l, r) => Or(groundSchemaF(l, init), groundSchemaF(r, init))
      case Neg(l) => Neg(groundSchemaF(l, init))
      case _ => throw new Exception("groundSchemaF")
    }

    // apply N-times And on a grounded f
    def andNSchemaF(f: SchemaFormula, init: Int, end: Int): SchemaFormula = {
      if (init == end)
        groundSchemaF(f, init)
      else {
        def list = (init to end).toList
        val l1 = list.map(i =>  {
          f match {
            case IndexedPredicate(_, _) => groundSchemaF(f, i)
            case And(l, r) => And(groundSchemaF(l, i), groundSchemaF(r, i))
            case Or(l, r) => Or(groundSchemaF(l, i), groundSchemaF(r, i))
            case Neg(l) => Neg(groundSchemaF(l, i))
            case _ => throw new Exception("andNSchemaF")
          }
        })
        l1.tail.foldLeft(l1.head)((x, res) => And(x, res))
      }
    }
}
