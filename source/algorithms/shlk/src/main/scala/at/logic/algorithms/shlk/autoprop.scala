package at.logic.algorithms.shlk

import at.logic.algorithms.lk.getAncestors
import at.logic.algorithms.lk.cleanStructuralRules
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.language.hol.{HOLConst, Atom, HOLExpression, HOLFormula}

//import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.lambda.types.{Ti, Tindex}

//convenient method for the iCERES project
object ContinueAutoProp {
  def apply(seq: FSequent): Option[LKProof] = {
    try {
      Some(Autoprop.apply(seq))
    } catch {
      case e:NoneException => {
        println("\n"+seq+" cannot be proved by propositional rules !\n")
        None
      }
    }
  }
}

class NoneException(s: String) extends Exception(s) {}

// continue autopropositional
object Autoprop {
  
  // This method is used in prooftool to test autopropositional feature.
  def apply(s: String): List[LKProof] = if (s.isEmpty) {
    val auto1 = apply1(test.apply())
    val auto2 = cleanStructuralRules(auto1)
    List(auto1,auto2)
  } else {
    val seq = SHLK.parseSequent(s)
    apply( seq ) :: Nil
  }
//Working on upgrading this function
  def apply(seq: FSequent): LKProof = {
    var p = apply1(seq)
    cleanStructuralRules(p)
  }

  def apply1(seq: FSequent): LKProof = {
    if (isSeqTautology(seq)) {
      val (f, rest) = getAxiomfromSeq(seq)
      return WeakeningRuleN(Axiom(f::Nil, f::Nil), rest)
    }

    if (getNonAtomicFAnt(seq) != None) {
      val f = getNonAtomicFAnt(seq).get._1
      val rest = getNonAtomicFAnt(seq).get._2
      f match {
        case Neg(f1) => return NegLeftRule(apply1(new FSequent(rest.antecedent, f1.asInstanceOf[HOLFormula] +: rest.succedent)), f1.asInstanceOf[HOLFormula])
        case Imp(f1, f2)=> {
          val up = ImpLeftRule(apply1(new FSequent(rest.antecedent, f1.asInstanceOf[HOLFormula] +: rest.succedent)), apply1(new FSequent(f2.asInstanceOf[HOLFormula] +: rest.antecedent, rest.succedent)), f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
          return ContractionRuleN(up, rest)
        }
        case And(f1, f2) => {
          val up1 = AndLeft1Rule(apply1(new FSequent(f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.antecedent, rest.succedent)), f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
          val up2 = AndLeft2Rule(up1, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
          return ContractionLeftRule(up2, f)
        }
        case Or(f1, f2) => {
          val t1 = apply1(new FSequent(f1.asInstanceOf[HOLFormula] +: rest.antecedent, rest.succedent))
          val t2 = apply1(new FSequent(f2.asInstanceOf[HOLFormula] +: rest.antecedent, rest.succedent))
          val up = OrLeftRule(t1, t2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
          return ContractionRuleN(up, rest)
        }
        case BigAnd(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to) {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return AndLeftEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = AndLeftRule(apply1(new FSequent(BigAnd(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            return AndLeftEquivalenceRule1(up, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
          }
        }
        case BigOr(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to){
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return OrLeftEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = OrLeftRule(apply1(new FSequent(BigOr(i, iter, from, Pred(to)) +:  rest.antecedent, rest.succedent)), apply1(new FSequent(subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            val up1 = ContractionRuleN(up, rest)
            return OrLeftEquivalenceRule1(up1, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
          }
        }
        case _ => throw new Exception("Error in ANT-case in Autoprop.apply1 !\n")
      }
    }

    if (getNonAtomicFSucc(seq) == None) {
      throw new NoneException("None")
    }


    val f = getNonAtomicFSucc(seq).get._1
    val rest = getNonAtomicFSucc(seq).get._2
    f match {
      case Neg(f1) => return NegRightRule(apply1(new FSequent(f1.asInstanceOf[HOLFormula] +: rest.antecedent, rest.succedent)), f1.asInstanceOf[HOLFormula])
      case Imp(f1, f2)=> {
        val up = ImpRightRule(apply1(new FSequent(f1.asInstanceOf[HOLFormula] +: rest.antecedent, f2.asInstanceOf[HOLFormula] +: rest.succedent)), f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
        return ContractionRuleN(up, rest)
      }
      case Or(f1, f2) => {
        val up1 = OrRight1Rule(apply1(new FSequent(rest.antecedent, f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.succedent)), f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
        val up2 = OrRight2Rule(up1, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
        return ContractionRightRule(up2, f)
      }
      case And(f1, f2) => {
        val t1 = apply1(new FSequent(rest.antecedent, f1.asInstanceOf[HOLFormula] +: rest.succedent))
        val t2 = apply1(new FSequent(rest.antecedent, f2.asInstanceOf[HOLFormula] +: rest.succedent))
        val up = AndRightRule(t1, t2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
        return ContractionRuleN(up, rest)
      }
      case BigAnd(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return AndRightEquivalenceRule3(apply1(new FSequent(rest.antecedent, subst(iter).asInstanceOf[SchemaFormula] +: rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = AndRightRule(apply1(new FSequent(rest.antecedent, BigAnd(i, iter, from, Pred(to)) +: rest.succedent)), apply1(new FSequent(rest.antecedent, subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          val up1 = ContractionRuleN(up, rest)
          return AndRightEquivalenceRule1(up1, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
        }
      }
      case BigOr(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to){
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return OrRightEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = OrRightRule(apply1(new FSequent(rest.antecedent, BigOr(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          return OrRightEquivalenceRule1(up, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
        }
      }
      case _ => throw new Exception("Error in SUCC-case in Autoprop.apply1 !\n")
    }
    throw new Exception("Error in Autoprop - missing case !")
  }

  def getListOfFormulasToContractAnt(seq: FSequent): Set[HOLFormula] = {
    seq.antecedent.filter(f => seq.antecedent.count(x => x == f) > 1).toSet
  }
  def getListOfFormulasToContractSucc(seq: FSequent): Set[HOLFormula] = {
    seq.succedent.filter(f => seq.succedent.count(x => x == f) > 1).toSet
  }

  def ContractionRuleN(p : LKProof, seq: FSequent) : LKProof = {
    var l1 = getListOfFormulasToContractAnt(p.root.toFSequent()).toList
    var up = p
    while(l1.length > 0) {
      up = l1.foldLeft(up)((res, f) => ContractionLeftRule(res, f))
      l1 = getListOfFormulasToContractAnt(up.root.toFSequent()).toList
    }
    var l2 = getListOfFormulasToContractSucc(p.root.toFSequent()).toList

    var up2 = up
    var i=1
    while(l2.length > 0) {
      i = i+1
      up2 = l2.foldLeft(up2)((res, f) => {
        ContractionRightRule(res, f)
      })
      l2 = getListOfFormulasToContractSucc(up2.root.toFSequent()).toList
    }
    up2
  }

  def WeakeningRuleN(p : LKProof, seq: FSequent) : LKProof = {
    val up = seq.antecedent.foldLeft(p)((res, f) => WeakeningLeftRule(res, f))
    seq.succedent.foldLeft(up)((res, f) => WeakeningRightRule(res, f))
  }

  //return the first non Atomic f-la and the subsequent without that f-la
  def getNonAtomicFAnt(seq: FSequent) : Option[(HOLFormula, FSequent)] = {
    seq.antecedent.foreach(f => f match {
      case IndexedPredicate(_, _) => {}
      case Atom(_ , arg) => {
        if ( arg.head.exptype == Ti())
          {  }
        else return Some(f, removeFfromSeqAnt(seq, f))
      }
      case _ => return Some(f, removeFfromSeqAnt(seq, f))
    })
    None
  }

  def getNonAtomicFSucc(seq: FSequent) : Option[(HOLFormula, FSequent)] = {
    seq.succedent.foreach(f => f match {
      case IndexedPredicate(_, _) => {}
      case Atom(_ , arg) => {
        if ( arg.head.exptype == Ti() )
          {  }
        else return Some(f, removeFfromSeqAnt(seq, f))
      }
      case _ => return Some(f, removeFfromSeqSucc(seq, f))
    })
    None
  }
  
  def isAtom(f: HOLFormula): Boolean = f match {
    case IndexedPredicate(_, _) => true
    case Atom(_, _) => true
    case _ => false
  }
  
  def isSeqTautology(seq: FSequent): Boolean = {
    seq.antecedent.foreach(f => seq.succedent.foreach(f2 =>  if(f == f2 && isAtom(f)) return true))
      return false
  }
  
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
    if (isSeqTautology(seq)) {
      seq.antecedent.foreach(f => if (seq.succedent.contains(f)){
        return (f, removeFfromSeqAnt(removeFfromSeqSucc(seq, f), f))
      })
      throw new Exception("\nError in if-autoprop.getAxiomfromSeq !\n")
    }
    else throw new Exception("\nError in else-autoprop.getAxiomfromSeq !\n")
  }
}

//**************************************************************************
object test {
  def apply(): FSequent = {
    val k = IntVar(new VariableStringSymbol("k"))
    val real_n = IntVar(new VariableStringSymbol("n"))
    val n = k
    val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
    val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
    val s = Set[FormulaOccurrence]()

    val i = IntVar(new VariableStringSymbol("i"))
    val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val B = IndexedPredicate(new ConstantStringSymbol("B"), i)
    val C = IndexedPredicate(new ConstantStringSymbol("C"), i)
    val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
    val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
    val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
    val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
    val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)

    val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

    val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
    val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
    val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

    val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
    val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
    val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
    val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
    val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
    //             println("\n\n START \n\n")

    //      val fseq = FSequent(A0 :: Nil, A0 :: Nil)
    //      val fseq = FSequent(A0 :: Neg(A0) :: Nil, Nil)
    val biga = BigAnd(i, A, zero, two)
    val bigo = BigOr(i, A, zero, one)
    val biga2 = BigAnd(i, A, zero, two)
    val bigo2 = BigOr(i, A, zero, two)

    //      val fseq = FSequent(bigo :: Nil, A0 :: A1 :: Nil )
    //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: Nil )
    //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: A2 :: Nil )
    //      val fseq = FSequent(A :: B :: Nil, And(A, B) :: Nil)
    val fseq = FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil)
//    val fseq = FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil)
//    val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil)
//    val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga :: Nil)
    //      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)
    fseq
  }
}
