package at.logic.algorithms.lk

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.{VariableNameGenerator, Var}
import at.logic.language.schema._
import at.logic.language.hol.{HOLConst, Atom, HOLExpression, HOLFormula}
import at.logic.language.lambda.types.{Ti, Tindex}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.lk.quantificationRules._

object solvePropositional {

  def apply(seq: FSequent): Option[LKProof] = prove(seq) match {
    case Some(p) =>
      //println("solvePropositional: # of contraction left rules: " + statistics.contLeftNumber(p))
      //println("solvePropositional: # of contraction right rules: " + statistics.contRightNumber(p))
      //println("solvePropositional: # of rules: " + statistics.rulesNumber(p))
      Some(CleanStructuralRules(p))
    case None => None
  }

  // Returns a boolean indicating if the sequent is provable.
  def isTautology(seq: FSequent) : Boolean = prove(seq) match {
    case Some(p) => true
    case None => false
  }

  // Method that throws an exception instead of returning None
  // Used in sFOparser.
  def autoProp(seq: FSequent) : LKProof = prove(seq) match {
    case Some(p) => CleanStructuralRules(p)
    case None => throw new Exception("Sequent is not provable.")
  }

  def prove(seq: FSequent): Option[LKProof] = {

    // Solving in this order:
    // 1. Check if its axiom
    // 2. Choose unary rule left
    // 3. Choose unary rule right
    // 4. Choose binary rule left
    // 5. Choose binary rule right

    if (isAxiom(seq)) {
      val (f, rest) = getAxiomfromSeq(seq)
      val p = addWeakenings(Axiom(f::Nil, f::Nil), seq)
      Some(p)
    }
    else findUnaryLeft(seq) match {
      // Apply unary rule on antecedent
      case Some(f) => 
      val rest = new FSequent(seq.antecedent.diff(f::Nil), seq.succedent)
      f match {

        case Neg(f1) =>
          // Computing premise antecedent and succedent
          val p_ant = rest.antecedent
          val p_suc = f1.asInstanceOf[HOLFormula] +: rest.succedent
          val premise = new FSequent(p_ant, p_suc)
          prove(premise) match {
            case Some(p) => 
              val p1 = NegLeftRule(p, f1.asInstanceOf[HOLFormula])
              Some(p1)
            case None => None
          }

        case And(f1, f2) => 
          // For this case, contract the formula and choose the first and then the second conjunct
          val up_ant = f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.antecedent
          val up_suc = rest.succedent
          val upremise = new FSequent(up_ant, up_suc)
          prove(upremise) match {
            case Some(proof) =>
              val proof_and2 = AndLeft2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_and1 = AndLeft1Rule(proof_and2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_contr = ContractionLeftRule(proof_and1, f)
              Some(proof_contr)
            case None => None
          }

        case BigAnd(i, iter, from, to) =>
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to) {
            val new_map = Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val sf = subst(iter).asInstanceOf[SchemaFormula]
            val p_ant = sf +: rest.antecedent
            val p_suc = rest.succedent
            val premise = new FSequent(p_ant, p_suc)
            prove(premise) match {
              case Some(proof) => 
                val proof2 = AndLeftEquivalenceRule3(proof, sf, f.asInstanceOf[SchemaFormula])
                Some(proof2)
              case None => None
            }
          }
          else {
            val new_map = Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val sf1 = BigAnd(i, iter, from, Pred(to))
            val sf2 = subst(iter).asInstanceOf[HOLFormula]
            val p_ant = sf1 +: sf2 +: rest.antecedent
            val p_suc = rest.succedent
            val premise = new FSequent(p_ant, p_suc)
            prove(premise) match {
              case Some(proof) =>
                val proof1 = AndLeftRule(proof, sf1, sf2)
                val and = And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
                val proof2 = AndLeftEquivalenceRule1(proof1, and, BigAnd(i, iter, from, to))
                Some(proof2)
              case None => None
            }
          }
      }

      case None => findUnaryRight(seq) match {
        // Apply unary rule on succedent
        case Some(f) =>
        val rest = new FSequent(seq.antecedent, seq.succedent.diff(f::Nil))
        f match {
        
          case Neg(f1) =>
            val p_ant = f1.asInstanceOf[HOLFormula] +: rest.antecedent
            val p_suc = rest.succedent
            val premise = new FSequent(p_ant, p_suc)
            prove(premise) match {
              case Some(p) => 
                val p1 = NegRightRule(p, f1.asInstanceOf[HOLFormula])
                Some(p1)
              case None => None
            }
  
          case Imp(f1, f2)=> 
            val p_ant = f1.asInstanceOf[HOLFormula] +: rest.antecedent
            val p_suc = f2.asInstanceOf[HOLFormula] +: rest.succedent
            val premise = new FSequent(p_ant, p_suc)
            prove(premise) match {
              case Some(p) => 
                val p1 = ImpRightRule(p, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                Some(p1)
              case None => None
            }
          
          case Or(f1, f2) => 
            // For this case, contract the formula and choose the first and then the second conjunct
            val up_ant = rest.antecedent
            val up_suc = f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.succedent
            val upremise = new FSequent(up_ant, up_suc)
            prove(upremise) match {
              case Some(proof) =>
                val proof_or2 = OrRight2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                val proof_or1 = OrRight1Rule(proof_or2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                val proof_contr = ContractionRightRule(proof_or1, f)
                Some(proof_contr)
              case None => None
            }
  
          case BigOr(i, iter, from, to) => 
            val i = IntVar(new VariableStringSymbol("i"))
            if (from == to){
              val new_map = Map[Var, HOLExpression]() + Pair(i, to)
              val subst = new SchemaSubstitution1[HOLExpression](new_map)
              val p_ant = subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent
              val p_suc = rest.succedent
              val premise = new FSequent(p_ant, p_suc)
              prove(premise) match {
                case Some(proof) =>
                  val proof1 = OrRightEquivalenceRule3(proof, subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
                  Some(proof1)
                case None => None
              }
            }
            else {
              val new_map = Map[Var, HOLExpression]() + Pair(i, to)
              val subst = new SchemaSubstitution1[HOLExpression](new_map)
              val p_ant = rest.antecedent
              val p_suc = BigOr(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +: rest.succedent
              val premise = new FSequent(p_ant, p_suc)
              prove(premise) match {
                case Some(proof) => 
                  val proof1 = OrRightRule(proof, BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
                  val or = Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
                  val proof2 = OrRightEquivalenceRule1(proof1, or, BigOr(i, iter, from, to))
                  Some(proof2)
                case None => None
              }
            }
  
          }

        case None => findBinaryLeft(seq) match {
          // Apply binary rule on antecedent
          case Some(f) =>
          val rest = new FSequent(seq.antecedent.diff(f::Nil), seq.succedent)
          f match {
            
            case Imp(f1, f2)=>
              val p_ant1 = rest.antecedent
              val p_suc1 = f1.asInstanceOf[HOLFormula] +: rest.succedent
              val p_ant2 = f2.asInstanceOf[HOLFormula] +: rest.antecedent
              val p_suc2 = rest.succedent
              val premise1 = new FSequent(p_ant1, p_suc1)
              val premise2 = new FSequent(p_ant2, p_suc2)
              (prove(premise1), prove(premise2)) match {
                case (Some(p1), Some(p2)) =>
                  val p = ImpLeftRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                  val p_contr = addContractions(p, seq)
                  Some(p_contr)
                case _ => None
              }
  
            case Or(f1, f2) => 
              val p_ant1 = f1.asInstanceOf[HOLFormula] +: rest.antecedent
              val p_suc1 = rest.succedent
              val p_ant2 = f2.asInstanceOf[HOLFormula] +: rest.antecedent
              val p_suc2 = rest.succedent
              val premise1 = new FSequent(p_ant1, p_suc1)
              val premise2 = new FSequent(p_ant2, p_suc2)
              (prove(premise1), prove(premise2)) match {
                case (Some(p1), Some(p2)) => 
                  val p = OrLeftRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                  val p_contr = addContractions(p, seq)
                  Some(p_contr)
                case _ => None
              }
  
            case BigOr(i, iter, from, to) =>
              val i = IntVar(new VariableStringSymbol("i"))
              if (from == to){
                val new_map = Map[Var, HOLExpression]() + Pair(i, to)
                val subst = new SchemaSubstitution1[HOLExpression](new_map)
                val sf = subst(iter).asInstanceOf[SchemaFormula]
                val p_ant = sf +: rest.antecedent
                val p_suc = rest.succedent
                val premise = new FSequent(p_ant, p_suc)
                prove(premise) match {
                  case Some(proof) => 
                    val proof1 = OrLeftEquivalenceRule3(proof, sf, f.asInstanceOf[SchemaFormula])
                    Some(proof1)
                  case None => None
                }
              }
              else {
                val new_map = Map[Var, HOLExpression]() + Pair(i, to)
                val subst = new SchemaSubstitution1[HOLExpression](new_map)
                val p_ant1 = BigOr(i, iter, from, Pred(to)) +: rest.antecedent
                val p_suc1 = rest.succedent
                val p_ant2 = subst(iter).asInstanceOf[HOLFormula] +: rest.antecedent
                val p_suc2 = rest.succedent
                val premise1 = new FSequent(p_ant1, p_suc1)
                val premise2 = new FSequent(p_ant2, p_suc2)
                (prove(premise1), prove(premise2)) match {
                  case (Some(proof1), Some(proof2)) =>
                    val proof3 = OrLeftRule(proof1, proof2, BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
                    val or = Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
                    val proof4 = OrLeftEquivalenceRule1(proof3, or, BigOr(i, iter, from, to))
                    val proof5 = addContractions(proof4, seq)
                    Some(proof5)
                  case _ => None
                }
              }
          }

          case None => findBinaryRight(seq) match {
            // Apply binary rule on succedent
            case Some(f) =>
            val rest = new FSequent(seq.antecedent, seq.succedent.diff(f::Nil))
            f match {

              case And(f1, f2) => 
                val p_ant1 = rest.antecedent
                val p_suc1 = f1.asInstanceOf[HOLFormula] +: rest.succedent
                val p_ant2 = rest.antecedent
                val p_suc2 = f2.asInstanceOf[HOLFormula] +: rest.succedent
                val premise1 = new FSequent(p_ant1, p_suc1)
                val premise2 = new FSequent(p_ant2, p_suc2)
                (prove(premise1), prove(premise2)) match {
                  case (Some(p1), Some(p2)) => 
                    val p = AndRightRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                    val p_contr = addContractions(p, seq)
                    Some(p_contr)
                  case _ => None
                }
    
              case BigAnd(i, iter, from, to) =>
                val i = IntVar(new VariableStringSymbol("i"))
                if (from == to) {
                  val new_map = Map[Var, HOLExpression]() + Pair(i, to)
                  val subst = new SchemaSubstitution1[HOLExpression](new_map)
                  val p_ant = rest.antecedent
                  val p_suc = subst(iter).asInstanceOf[SchemaFormula] +: rest.succedent
                  val premise = new FSequent(p_ant, p_suc)
                  prove(premise) match {
                    case Some(proof) =>
                      val proof1 = AndRightEquivalenceRule3(proof, subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
                      Some(proof1)
                    case None => None
                  }
                }
                else {
                  val new_map = Map[Var, HOLExpression]() + Pair(i, to)
                  val subst = new SchemaSubstitution1[HOLExpression](new_map)
                  val p_ant1 = rest.antecedent
                  val p_suc1 = BigAnd(i, iter, from, Pred(to)) +: rest.succedent
                  val p_ant2 = rest.antecedent
                  val p_suc2 = subst(iter).asInstanceOf[HOLFormula] +: rest.succedent
                  val premise1 = new FSequent(p_ant1, p_suc1)
                  val premise2 = new FSequent(p_ant2, p_suc2)
                  (prove(premise1), prove(premise2)) match {
                    case (Some(proof1), Some(proof2)) =>
                      val proof3 = AndRightRule(proof1, proof2, BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
                      val and = And(BigAnd(i, iter, from, Pred(to)),  subst(iter).asInstanceOf[SchemaFormula])
                      val proof4 = AndRightEquivalenceRule1(proof3, and, BigAnd(i, iter, from, to))
                      val proof5 = addContractions(proof4, seq)
                      Some(proof5)
                    case _ => None
                  }
                }
            }

            // No proof found
            case None => None

          }
        }
      }
    }
  }

  // Checks if the sequent is of the form A, \Gamma |- A, \Delta
  def isAxiom(seq: FSequent): Boolean = 
    seq.antecedent.exists(f => 
      seq.succedent.exists(f2 => 
        f == f2 && f.isAtom
      )
    )
 
  // Tries to find a formula on the left or on the right such that its
  // introduction rule is unary.
  def findUnaryLeft(seq: FSequent) : Option[HOLFormula] =
    seq.antecedent.find(f => f match {
      case Neg(_) | And(_,_) | BigAnd(_,_,_,_) => true
      case _ => false
    }) 
  def findUnaryRight(seq: FSequent) : Option[HOLFormula] =
    seq.succedent.find(f => f match {
      case Neg(_) | Imp(_,_) | Or(_,_) | BigOr(_,_,_,_) => true
      case _ => false
    })

  // Tries to find a formula on the left or on the right such that its
  // introduction rule is binary.
  def findBinaryLeft(seq: FSequent) : Option[HOLFormula] =
    seq.antecedent.find(f => f match {
      case Imp(_,_) | Or(_,_) | BigOr(_,_,_,_) => true
      case _ => false
    })  
  def findBinaryRight(seq: FSequent) : Option[HOLFormula] =
    seq.succedent.find(f => f match {
      case And(_,_) | BigAnd(_,_,_,_) => true
      case _ => false
    })

  def removeFfromSeqAnt(seq: FSequent, f : HOLFormula) : FSequent = {
    new FSequent(seq.antecedent.filter(x => x != f) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, f : HOLFormula) : FSequent = {
    new FSequent(seq.antecedent, seq.succedent.filter(x => x != f))
  }

  def removeFfromSeqAnt(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    new FSequent(seq.antecedent.filter(x => !flist.contains(x)) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    new FSequent(seq.antecedent, seq.succedent.filter(x => !flist.contains(x)))
  }
  
  def getAxiomfromSeq(seq: FSequent) : (HOLFormula, FSequent) = {
    if (isAxiom(seq)) {
      seq.antecedent.foreach(f => if (seq.succedent.contains(f)){
        return (f, removeFfromSeqAnt(removeFfromSeqSucc(seq, f), f))
      })
      throw new Exception("\nError in if-autoprop.getAxiomfromSeq !\n")
    }
    else throw new Exception("\nError in else-autoprop.getAxiomfromSeq !\n")
  }


}

object AtomicExpansion {
  import at.logic.language.hol._

  /*  === implements algorithm from Lemma 4.1.1 in Methods of Cut-Elimination === */
  /* given a sequent S = F :- F for an arbitrary formula F, derive a proof of S from atomic axioms
   * CAUTION: Does not work on schematic formulas! Reason: No match for BigAnd/BigOr, schema substitution is special. */
  def apply(fs : FSequent) : LKProof = {
    //find a formula occurring on both sides
    val occurs_on_both_sides = for (left <- fs.antecedent.toList;
                                    right <- fs.succedent.toList;
                                    if (left == right)) yield ((left,right))

    if (occurs_on_both_sides.isEmpty) throw new Exception("Could not find a formula in "+fs+" which occurs on both sides!")
    val (f1,f2)::_ = occurs_on_both_sides

    //initialize generator for eigenvariables
    var index = 100
    val gen = new VariableNameGenerator(() => { index = index+1; "ev"+index+""} )

    val atomic_proof = atomicExpansion_(gen, f1,f2)
    val FSequent(missingleft,missingright) = fs diff atomic_proof.root.toFSequent
    val weakenedleft  = missingleft.foldLeft(atomic_proof)((p,f) => WeakeningLeftRule(p,f))
    val weakenedright = missingright.foldLeft(weakenedleft)((p,f) => WeakeningRightRule(p,f))
    weakenedright
  }

  // assumes f1 == f2
  private def atomicExpansion_(gen : VariableNameGenerator ,f1 : HOLFormula, f2: HOLFormula) : LKProof = {
    try {
      (f1,f2) match {
        case (Neg(l1), Neg(l2)) =>
          val parent = atomicExpansion_(gen, l1,l2)
          NegLeftRule(NegRightRule(parent,l1 ), l2)

        case (And(l1,r1), And(l2,r2) ) =>
          val parent1 = atomicExpansion_(gen, l1,l2)
          val parent2 = atomicExpansion_(gen, r1,r2)
          val i1 = AndLeft1Rule(parent1, l1, r1)
          val i2 = AndLeft2Rule(parent2, l2, r2)
          val i3 = AndRightRule(i1,i2,l1,r1)
          ContractionLeftRule(i3, f1)

        case (Or(l1,r1), Or(l2,r2) ) =>
          val parent1 = atomicExpansion_(gen, l1,l2)
          val parent2 = atomicExpansion_(gen, r1,r2)
          val i1 = OrRight1Rule(parent1, l1, r1)
          val i2 = OrRight2Rule(parent2, l2, r2)
          val i3 = OrLeftRule(i1,i2,l1,r1)
          ContractionRightRule(i3,f1)

        case (Imp(l1,r1), Imp(l2,r2) ) =>
          val parent1 = atomicExpansion_(gen, l1,l2)
          val parent2 = atomicExpansion_(gen, r1,r2)
          val i1 = ImpLeftRule(parent1, parent2, l1, r1)
          ImpRightRule(i1, l2,r2)

        case (AllVar(x1:HOLVar,l1), AllVar(x2:HOLVar,l2)) =>
          val eigenvar = gen(x1, List(l1,l2)).asInstanceOf[HOLVar]
          val sub1 = Substitution[HOLExpression](List((x1,eigenvar)))
          val sub2 = Substitution[HOLExpression](List((x2,eigenvar)))
          val aux1 = sub1(l1).asInstanceOf[HOLFormula]
          val aux2 = sub2(l2).asInstanceOf[HOLFormula]

          val parent = atomicExpansion_(gen, aux1, aux2)
          val i1 = ForallLeftRule(parent, aux1, f1, eigenvar)
          ForallRightRule(i1, aux2, f2, eigenvar)

        case (ExVar(x1:HOLVar,l1), ExVar(x2:HOLVar,l2)) =>
          val eigenvar = gen(x1, List(l1,l2)).asInstanceOf[HOLVar]
          val sub1 = Substitution[HOLExpression](List((x1,eigenvar)))
          val sub2 = Substitution[HOLExpression](List((x2,eigenvar)))
          val aux1 = sub1(l1).asInstanceOf[HOLFormula]
          val aux2 = sub2(l2).asInstanceOf[HOLFormula]

          val parent = atomicExpansion_(gen, aux1, aux2)
          val i1 = ExistsRightRule(parent, aux2, f2, eigenvar)
          ExistsLeftRule(i1, aux1, f1, eigenvar)

        case (a1,a2) if a1.isAtom && a2.isAtom =>
          Axiom(a1::Nil, a2::Nil)

        case _ =>
          throw new Exception(""+f1+" and "
            +f2+" do not have the same outermost operator or operator unhandled!")

      }
    } catch {
      case e:Exception =>
        throw new Exception("Error in non-atomic axiom expansion handling "+ f1 + " and "+f2+": "+e.getMessage, e)
    }
  }
}


