/*
 * Struct.scala
 *
 */

package at.logic.transformations.ceres.struct

import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import at.logic.algorithms.shlk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.{LabelledSequent, UnaryLKskProof, LabelledFormulaOccurrence}
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.calculi.slk._
import at.logic.language.hol.{Substitution => HOLSubstitution, _}
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.SymbolA
import at.logic.language.schema.{Substitution => SchemaSubstitution, SchemaFormula, BiggerThan, IntZero, IntVar, IntegerTerm, IndexedPredicate, Succ, TopC, BigAnd, BigOr, Pred, SchemaVar}
import at.logic.utils.ds.Multisets.Multiset
import at.logic.utils.ds.Multisets._
import at.logic.utils.ds.trees._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet._
import at.logic.transformations.ceres.RelevantCC
import scala.collection.immutable.HashSet
import scala.math.max

trait Struct {
  def formula_equal(that: Struct) : Boolean;
  def size() : Int; //total number of nodes
  def alternations() : Int; //number of alternations (includes duals)
}

  // Times is done as an object instead of a case class since
  // it has a convenience constructor (with empty auxFOccs)
  object Times
  {
    def apply(left: Struct, right: Struct, auxFOccs: List[FormulaOccurrence]) : Times =
      new Times(left, right, auxFOccs)
   
    def apply(left: Struct, right: Struct) : Times =
      apply(left, right, Nil)

    def unapply(s: Struct) = s match {
      case t : Times => Some((t.left, t.right, t.auxFOccs))
      case _ => None
    }
  }

  class Times(val left: Struct, val right: Struct, val auxFOccs: List[FormulaOccurrence]) extends Struct {
    override def toString(): String = Console.RED+"("+Console.RESET+left+Console.RED+" ⊗ "+Console.RESET+right+Console.RED+")"+Console.RESET
    override def formula_equal(s:Struct) = s match {
      case Times(x,y,aux) => left.formula_equal(x) && right.formula_equal(y) &&
        aux.diff(auxFOccs).isEmpty && auxFOccs.diff(aux).isEmpty
      case _ => false
    }

    override def size() = 1 + left.size() + right.size()
    override def alternations() = {
      (left,right) match {
        case (Times(_,_,_), Times(_,_,_)) => max(left.alternations(), right.alternations())
        case (Times(_,_,_), _) => max(left.alternations(), 1+right.alternations())
        case (_, Times(_,_,_)) => max(1+left.alternations(), right.alternations())
        case _ => 1+ max(left.alternations(), right.alternations())
      }
    }

  }

  case class Plus(left: Struct, right: Struct) extends Struct {
    override def toString(): String = Console.BLUE+"("+Console.RESET+left+Console.BLUE+" ⊕ "+Console.RESET+right+Console.BLUE+")"+Console.RESET
    override def formula_equal(s:Struct) = s match {
      case Plus(x,y) => left.formula_equal(x) && right.formula_equal(y)
      case _ => false
    }
    override def size() = 1 + left.size() + right.size()
    override def alternations() = {
      (left,right) match {
        case (Plus(_,_), Plus(_,_)) => max(left.alternations(), right.alternations())
        case (Plus(_,_), _) => max(left.alternations(), 1+right.alternations())
        case (_, Plus(_,_)) => max(1+left.alternations(), right.alternations())
        case _ => 1+ max(left.alternations(), right.alternations())
      }
    }
  }
  case class Dual(sub: Struct) extends Struct {
    override def toString(): String = Console.GREEN+"~("+Console.RESET+sub+Console.GREEN+")"+Console.RESET
    override def formula_equal(s:Struct) = s match {
      case Dual(x) => sub.formula_equal(x)
      case _ => false
    }
    override def size() = 1 + sub.size()
    override def alternations() = {
      sub match {
        case Dual(_) =>  sub.alternations
        case _ => 1+sub.size
      }
    }
  }
  case class A(fo: FormulaOccurrence) extends Struct {// Atomic Struct
    override def toString(): String =fo.formula.toString
    override def formula_equal(s:Struct) = s match {
      case A(x) => fo.formula syntaxEquals(x.formula)
      case _ => false
    }

    override def size() = 1
    override def alternations() = 0
  }
  case class EmptyTimesJunction() extends Struct {
    override def toString(): String = Console.RED+"ε"+Console.RESET
    override def formula_equal(s:Struct) = s match {
      case EmptyTimesJunction() => true
      case _ => false
    }
    override def size() = 1
    override def alternations() = 0
  }
  case class EmptyPlusJunction() extends Struct {
    override def toString(): String = Console.BLUE+"ε"+Console.RESET
    override def formula_equal(s:Struct) = s match {
      case EmptyPlusJunction() => true
      case _ => false
    }
    override def size() = 1
    override def alternations() = 0
  }

  /* convenience object allowing to create and match a set of plus nodes */
  object PlusN {
    def apply(l : List[Struct]) : Struct = l match {
      case Nil => EmptyPlusJunction()
      case x::Nil => x
      case x::xs =>  Plus(x,PlusN(xs))
    }


    def unapply(s:Struct) : Option[List[Struct]] = Some(unapply_(s))

    def unapply_(s:Struct) : List[Struct] = s match {
      case Plus(l,r) => unapply_(l) ++ unapply_(r)
      case _ => s::Nil
    }
  }



  // since case classes may be DAGs, we give a method to convert to a tree
  // (for, e.g. displaying purposes)

  object structToExpressionTree {
    def apply(s: Struct) : Tree[HOLExpression] = s match
    {
      case A(f) => LeafTree(f.formula)
      case Dual(sub) => UnaryTree(DualC, apply(sub))
      case Times(left, right, _) => BinaryTree(TimesC, apply(left), apply(right))
      case Plus(left, right) => BinaryTree(PlusC, apply(left), apply(right))
      case EmptyTimesJunction() => LeafTree(EmptyTimesC)
      case EmptyPlusJunction() => LeafTree(EmptyPlusC)
    }

    // constructs struct Tree without empty leaves.
    def prunedTree(s: Struct) : Tree[HOLExpression] = s match
    {
      case A(f) => LeafTree(f.formula)
      case Dual(sub) => UnaryTree(DualC, prunedTree(sub))
      case Times(left, right, _) =>
        val l = prunedTree(left)
        val r = prunedTree(right)
        if (l.isInstanceOf[LeafTree[HOLExpression]] && (l.vertex == EmptyTimesC || l.vertex == EmptyPlusC))
          if (r.isInstanceOf[LeafTree[HOLExpression]] && (r.vertex == EmptyTimesC || r.vertex == EmptyPlusC)) LeafTree(EmptyTimesC)
          else r
        else if (r.isInstanceOf[LeafTree[HOLExpression]] && (r.vertex == EmptyTimesC || r.vertex == EmptyPlusC)) l
        else BinaryTree(TimesC, l, r)
      case Plus(left, right) =>
        val l = prunedTree(left)
        val r = prunedTree(right)
        if (l.isInstanceOf[LeafTree[HOLExpression]] && (l.vertex == EmptyTimesC || l.vertex == EmptyPlusC))
          if (r.isInstanceOf[LeafTree[HOLExpression]] && (r.vertex == EmptyTimesC || r.vertex == EmptyPlusC)) LeafTree(EmptyPlusC)
          else r
        else if (r.isInstanceOf[LeafTree[HOLExpression]] && (r.vertex == EmptyTimesC || r.vertex == EmptyPlusC)) l
        else BinaryTree(PlusC, l, r)
      case EmptyTimesJunction() => LeafTree(EmptyTimesC)
      case EmptyPlusJunction() => LeafTree(EmptyPlusC)
    }

    // We define some symbols that represent the operations of the struct

    case object TimesSymbol extends LogicalSymbolA {
      override def unique = "TimesSymbol"
      override def toString = "⊗"
      def toCode = "TimesSymbol"
    }

    case object PlusSymbol extends LogicalSymbolA {
      override def unique = "PlusSymbol"
      override def toString = "⊕"
      def toCode = "PlusSymbol"
    }

    case object DualSymbol extends LogicalSymbolA {
      override def unique = "DualSymbol"
      override def toString = "∼"
      def toCode = "DualSymbol"
    }

    case object EmptyTimesSymbol extends LogicalSymbolA {
      override def unique = "EmptyTimesSymbol"
      override def toString = "ε_⊗"
      def toCode = "EmptyTimesSymbol"
    }

    case object EmptyPlusSymbol extends LogicalSymbolA {
      override def unique = "EmptyPlusSymbol"
      override def toString = "ε_⊕"
      def toCode = "EmptyPlusSymbol"
    }

    case object TimesC extends HOLConst(TimesSymbol, Type("( o -> (o -> o) )"))
    case object PlusC extends HOLConst(PlusSymbol, Type("( o -> (o -> o) )"))
    case object DualC extends HOLConst(DualSymbol, Type("(o -> o)"))
    case object EmptyTimesC extends HOLConst(EmptyTimesSymbol, To)
    case object EmptyPlusC extends HOLConst(EmptyPlusSymbol, To)
  }

  // some stuff for schemata

  // cut configurations: one using multisets of formulas (to relate different proof definitions)
  // and one using FormulaOccurrences (if we are only considering a single proof definition)
  object TypeSynonyms {
    type CutConfiguration = (Multiset[HOLFormula], Multiset[HOLFormula])
    type CutOccurrenceConfiguration = Set[FormulaOccurrence]
  }
  object cutConfToString { 
    def apply(cc : TypeSynonyms.CutConfiguration) = {
      def str( m : Multiset[HOLFormula] ) = m.foldLeft( "" )( (s, f) => s + {if (s != "") ", " else ""} + f.toString )
      str( cc._1 ) + " | " + str( cc._2 )
    }
  }


// Takes a CutOccurrenceConfiguration and creates a CutConfiguration cc
  // by, for each o in cc, taking the element f from seq such that
  // f, where param goes to term, is equal to o.formula.
  object cutOccConfigToCutConfig {
    def apply( so: Sequent, cc: TypeSynonyms.CutOccurrenceConfiguration, seq: FSequent, params: List[IntVar], terms: List[IntegerTerm]): (Multiset[HOLFormula], Multiset[HOLFormula]) = {
      cc.foldLeft( (HashMultiset[HOLFormula](), HashMultiset[HOLFormula]() ) )( (res, fo) => {
        val cca = res._1
        val ccs = res._2
        if (so.antecedent.map(x => x.formula).contains( fo.formula ))
          (cca + getFormulaForCC( fo, seq._1.asInstanceOf[List[HOLFormula]], params, terms ), ccs)
        else
          if (so.succedent.map(x => x.formula).contains( fo.formula ))
            (cca, ccs + getFormulaForCC( fo, seq._2.asInstanceOf[List[HOLFormula]], params, terms ))
          else
            throw new Exception("\nError in cutOccConfigToCutConfig !\n")
      })
    }

    def applyRCC( so: Sequent, cc: TypeSynonyms.CutOccurrenceConfiguration): (Multiset[HOLFormula], Multiset[HOLFormula]) = {
      if(cc.isEmpty)
        return (HashMultiset[HOLFormula](), HashMultiset[HOLFormula]() )
      val seq = so.toFSequent
      val params = IntVar("k")::Nil
      val terms = IntVar("k")::Nil
      cc.foldLeft( (HashMultiset[HOLFormula](), HashMultiset[HOLFormula]() ) )( (res, fo) => {
        val cca = res._1
        val ccs = res._2
        if (so.antecedent.map(x => x.formula).contains( fo.formula ))
          (cca + getFormulaForCC( fo, seq._1.asInstanceOf[List[HOLFormula]], params, terms ), ccs)
        else
        if (so.succedent.map(x => x.formula).contains( fo.formula ))
          (cca, ccs + getFormulaForCC( fo, seq._2.asInstanceOf[List[HOLFormula]], params, terms ))
        else
          throw new Exception("\nError in cutOccConfigToCutConfigRCC !\n")
      })
    }

    def getFormulaForCC( fo: FormulaOccurrence, fs: List[HOLFormula], params: List[IntVar], terms: List[IntegerTerm] ) =
    {
      val sub = HOLSubstitution(params.zip(terms))

      val list = fs.filter( f => {
        sub(f).syntaxEquals(fo.formula) || f.syntaxEquals(fo.formula)
      }) 
      list match {
        case Nil => {
          throw new Exception("Could not find a formula to construct the cut-configuration!")
        }
        case x::_ => x
      }
    }
  }

  // In the construction of schematized clause sets, we use symbols
  // that contain a name and a cut-configuration. This class represents
  // such symbols.
  class ClauseSetSymbol(val name: String, val cut_occs: TypeSynonyms.CutConfiguration) extends SymbolA {

    override def toString() = {
      val nice_name:String = name match {
        case "\\psi" | "psi" => "ψ"
        case "\\chi" | "chi" => "χ"
        case "\\varphi" |"varphi" => "φ"
        case "\\phi" |"phi" => "ϕ"
        case "\\rho" |"rho" => "ρ"
        case "\\sigma" |"sigma" => "σ"
        case "\\tau" | "tau" => "τ"
        case _ => name
      }
      "cl^{"+ nice_name + ",(" + cutConfToString(cut_occs) + ")}"
    }
  }

  object StructCreators {
    def size(s:Struct) : Int = size(s,0)
    //TODO:make tailrecursive
    def size(s:Struct, n:Int) : Int = s match {
      case A(_) => n
      case Dual(x) => size(x,n+1)
      case Plus(l,r) => size(l, size(r,n+1))
      case Times(l,r,_) => size(l, size(r,n+1))
      case EmptyPlusJunction() => n
      case EmptyTimesJunction() => n
    }

    // this is for proof schemata: it extracts the characteristic
    // clause set for the proof called "name"
    // fresh_param should be fresh

    def extractFormula(name: String, fresh_param: IntVar) : HOLFormula =
    {
      val cs_0_f = SchemaProofDB.foldLeft[HOLFormula](TopC)((f, ps) =>
        And(cutConfigurations( ps._2.base ).foldLeft[HOLFormula](TopC)((f2, cc) =>
          And(Imp(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.base.root, cc, ps._2.seq, ps._2.vars, IntZero()::Nil ) ), 
                                   IntZero()::Nil ),
                  toFormula(extractBaseWithCutConfig(ps._2, cc))), f2)),
            f) )

      // assumption: all proofs in the SchemaProofDB have the
      // same running variable "k".
      val k = IntVar("k")
      val cs_1_f = SchemaProofDB.foldLeft[HOLFormula](TopC)((f, ps) =>
        And(cutConfigurations( ps._2.rec ).foldLeft[HOLFormula](TopC)((f2, cc) =>
          And(Imp(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.rec.root, cc, ps._2.seq, ps._2.vars, Succ(k)::Nil ) ), 
                                   Succ(k)::Nil ),
                  toFormula(extractStepWithCutConfig(ps._2, cc))), f2)
              ),
            f) )

      val cl_n = IndexedPredicate( new ClauseSetSymbol(name, (HashMultiset[HOLFormula], HashMultiset[HOLFormula]) ),
                                   fresh_param::Nil )
      And(cl_n, And( cs_0_f , BigAnd( k, cs_1_f.asInstanceOf[SchemaFormula], IntZero(), fresh_param )))
    }

    def toFormula(s: Struct) : HOLFormula =
      transformStructToClauseSet( s ).foldLeft[HOLFormula](TopC)((f, c) =>
        And(f, toFormula(c)))

    // FIXME: this method should not exist.
    // it's a workaround necessary since so far, the logical
    // constants are not created by the factories, and hence
    // do not work across language-levels, but the constants
    // are neede to transform a sequent to a formula in general.
    def toFormula( s: Sequent ) : HOLFormula =
      Or( s.antecedent.map( f => Neg( f.formula.asInstanceOf[HOLFormula] )).toList ++ (s.succedent map (_.formula.asInstanceOf[HOLFormula])) )

    def extractRelevantStruct(name: String, fresh_param: IntVar): Tuple2[List[(String,  Struct, Set[FormulaOccurrence])], List[(String,  Struct, Set[FormulaOccurrence])]] = {
      val rcc = RelevantCC(name)._1.flatten
      val rez_step = rcc.map(pair => Tuple3("Θ(" + pair._1 + "_step, (" +
        cutConfToString( cutOccConfigToCutConfig( SchemaProofDB.get(pair._1).rec.root, pair._2, SchemaProofDB.get(pair._1).seq, SchemaProofDB.get(pair._1).vars, Succ(IntVar("k"))::Nil ) ) + "))",
        extractStepWithCutConfig( SchemaProofDB.get(pair._1), pair._2),
        pair._2))

      val rcc1 = RelevantCC(name)._2.flatten
      val rez_base = rcc1.map(pair => Tuple3("Θ(" + pair._1 + "_base, (" +
        cutConfToString( cutOccConfigToCutConfig( SchemaProofDB.get(pair._1).base.root, pair._2, SchemaProofDB.get(pair._1).seq, SchemaProofDB.get(pair._1).vars, IntZero()::Nil ) ) + "))",
        extractBaseWithCutConfig( SchemaProofDB.get(pair._1), pair._2),
        pair._2))
      Tuple2(rez_step, rez_base)
    }

    private def hackGettingProof(s: String) : SchemaProof = {
      val s1 = s.replace("Θ(","")
      val s2 = s1.replace("_base","\n")
      val s3 = s2.replace("_step","\n")
      val s4 = s3.takeWhile(c => !c.equals('\n'))
      SchemaProofDB.get( s4 )
    }
    
    def extractStruct(name: String, fresh_param: IntVar) : Struct = {
      val terms = extractRelevantStruct(name, fresh_param)
      val cs_0 = terms._2.foldLeft[Struct](EmptyPlusJunction())((result, triple) =>
          Plus(Times(Dual(A(toOccurrence(IndexedPredicate( new ClauseSetSymbol( triple._1.replace("Θ(","").replace("_base","\n").takeWhile(c => !c.equals('\n')),
            cutOccConfigToCutConfig( hackGettingProof(triple._1).base.root, triple._3, hackGettingProof(triple._1).seq, hackGettingProof(triple._1).vars, IntZero()::Nil ) ), IntZero()::Nil ), hackGettingProof(triple._1).base.root ) ) ),
            triple._2), result) )

      // assumption: all proofs in the SchemaProofDB have the
      // same running variable "k".
      val k = IntVar("k")
      val cs_1 = terms._1.foldLeft[Struct](EmptyPlusJunction())((result, triple) =>
        Plus(Times(Dual(A(toOccurrence(IndexedPredicate( new ClauseSetSymbol( triple._1.replace("Θ(","").replace("_step","\n").takeWhile(c => !c.equals('\n')),
          cutOccConfigToCutConfig( hackGettingProof(triple._1).rec.root, triple._3, hackGettingProof(triple._1).seq, hackGettingProof(triple._1).vars, Succ(k)::Nil ) ), Succ(k)::Nil ), hackGettingProof(triple._1).rec.root ) ) ),
          triple._2), result) )

      val cl_n = IndexedPredicate( new ClauseSetSymbol(name, (HashMultiset[HOLFormula], HashMultiset[HOLFormula]) ),
        fresh_param::Nil )
      Plus(A(toOccurrence(cl_n, SchemaProofDB.get(name).rec.root)), Plus( cs_0 ,cs_1) )
    }

    //extracts the struct given the relevant CC
    def extractStructRCCstep(name: String, fresh_param: IntVar, rcc: List[(String, Set[FormulaOccurrence])]) : Struct = {
      val relevant_struct_list_step = rcc.map(pair => Tuple3("Θ(" + pair._1 + "_step, (" +
        cutConfToString( cutOccConfigToCutConfig.applyRCC( SchemaProofDB.get(pair._1).rec.root, pair._2 ) ) + "))",
        extractStepWithCutConfig( SchemaProofDB.get(pair._1), pair._2),
        pair._2))
      val k = IntVar("k")
      val cs_0 = relevant_struct_list_step.foldLeft[Struct](EmptyPlusJunction())((result, triple) =>
        Plus(Times(Dual(A(toOccurrence(IndexedPredicate( new ClauseSetSymbol( triple._1.replace("Θ(","").replace("_step","\n").takeWhile(c => !c.equals('\n')),
          cutOccConfigToCutConfig.applyRCC( hackGettingProof(triple._1).rec.root, triple._3 ) ), Succ(k)::Nil ), hackGettingProof(triple._1).rec.root ) ) ),
          triple._2), result) )

      return cs_0
    }

    //the third parameter is for creating the cl symbols with the correct configuration
    def extractStructRCCbase(name: String, rcc: List[(String, Set[FormulaOccurrence], Set[FormulaOccurrence])]) : Struct = {
      val relevant_struct_list_base = rcc.map(triple =>
          if (triple._2 == triple._3)
            Tuple4("Θ(" + triple._1 + "_base, (" +
            cutConfToString( cutOccConfigToCutConfig.applyRCC( SchemaProofDB.get(triple._1).base.root, triple._3 ) ) + "))",
            extractBaseWithCutConfig( SchemaProofDB.get(triple._1), triple._2),
            triple._2, triple._3)
          else
            Tuple4("Θ(" + triple._1 + "_base, (" +
            cutConfToString( cutOccConfigToCutConfig.applyRCC( SchemaProofDB.get(triple._1).rec.root, triple._3 ) ) + "))",
            extractBaseWithCutConfig( SchemaProofDB.get(triple._1), triple._2),
            triple._2, triple._3)
      )

      println("\nrelevant_struct_list_base : "+relevant_struct_list_base)
      //the triple is here 4-ple
      val cs_0 = relevant_struct_list_base.foldLeft[Struct](EmptyPlusJunction())((result, fourple) =>
        if (fourple._3 == fourple._4)
          Plus(Times(Dual(A(toOccurrence(
            IndexedPredicate( new ClauseSetSymbol( fourple._1.replace("Θ(","").replace("_base","\n").takeWhile(c => !c.equals('\n')),
              cutOccConfigToCutConfig.applyRCC( hackGettingProof(fourple._1).base.root, fourple._4 ) ), IntZero()::Nil ),
            hackGettingProof(fourple._1).base.root ) ) ),
            fourple._2), result)
        else
          Plus(Times(Dual(A(toOccurrence(
            IndexedPredicate( new ClauseSetSymbol( fourple._1.replace("Θ(","").replace("_base","\n").takeWhile(c => !c.equals('\n')),
              cutOccConfigToCutConfig.applyRCC( hackGettingProof(fourple._1).rec.root, fourple._4 ) ), IntZero()::Nil ),
            hackGettingProof(fourple._1).base.root ) ) ),
            fourple._2), result)

      )
      return cs_0
    }



    // TODO: refactor --- this method should be somewhere else
    // some combinatorics: return the set of all sets
    // that can be obtained by drawing at most n elements
    // from a given set

    def combinations[A]( n: Int, m: Set[A] ) : Set[Set[A]] = n match {
      case 0 => HashSet() + HashSet()
      case _ => m.foldLeft( HashSet[Set[A]]() )( (res, elem) => {
        val s = combinations( n - 1, m - elem )
        res ++ s ++ s.map( m => m + elem )
      } )
    }

//    computes all cut configurations
    def cutConfigurations( p: LKProof ) = {
      val occs = p.root.antecedent ++ p.root.succedent
      combinations( occs.size, occs.toSet )
    }
    
    def extractStepWithCutConfig( schema: SchemaProof, cc: TypeSynonyms.CutOccurrenceConfiguration ) =
    {
      extract( schema.rec, getAncestors( cc ) ++ getCutAncestors( schema.rec ) )
    }

    def extractBaseWithCutConfig( schema: SchemaProof, cc: TypeSynonyms.CutOccurrenceConfiguration ) =
    {
      extract( schema.base, getAncestors( cc ) ++ getCutAncestors( schema.base ) )
    }

    // TODO this should really disappear.
    def toOccurrence( f: HOLFormula, so: Sequent ) =
    {
      defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, Nil)
    }

    def extract(p: LKProof) : Struct = extract( p, getCutAncestors( p ) )
    def extract(p: LKProof, predicate: HOLFormula => Boolean) : Struct = extract( p, getCutAncestors( p, predicate ) )

    private def debug(s:String) = { /* println("DEBUG:"+s) */ }

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
      {
        debug("0 "+cut_occs+ "  ");
        so match {
        case lso : LabelledSequent  if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 =>
          handleLabelledAxiom( lso, cut_occs )
        case _ => handleAxiom( so, cut_occs )
      }         }
      case UnaryLKProof(_,upperProof,_,_,_) =>{
        debug("1 "+cut_occs+ "  ");
        handleUnary( upperProof, cut_occs )     }
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) =>
        debug("2 "+cut_occs+ "  ");
        handleBinary( upperProofLeft, upperProofRight, aux1::aux2::Nil, cut_occs )
      case UnaryLKskProof(_,upperProof,_,_,_) =>
        debug("3 "+cut_occs+ "  ");
        handleUnary( upperProof, cut_occs )
      case UnarySchemaProof(_,upperProof,_,_,_) =>
        debug("4 "+cut_occs+ "  "); handleUnary( upperProof, cut_occs )
      case SchemaProofLinkRule(so, name, indices) =>
        debug("5 "+cut_occs+ "  ");
        handleSchemaProofLink( so, name, indices.asInstanceOf[List[IntegerTerm]], cut_occs )
      case TermEquivalenceRule1(upperProof, _, _, _) =>
        debug("6 "+cut_occs+ "  ");
        extract(upperProof, cut_occs)
      case ForallHyperLeftRule(upperProof, r, a, p, _) =>
        debug("7 "+cut_occs+ "  ");
        extract(upperProof, cut_occs)
      case ExistsHyperRightRule(upperProof, r, a, p, _) =>
        debug("8 "+cut_occs+ "  ");
        extract(upperProof, cut_occs)
      case ForallHyperRightRule(upperProof, r, a, p, _) =>
        debug("9 "+cut_occs+ "  ");
        extract(upperProof, cut_occs)
      case ExistsHyperLeftRule(upperProof, r, a, p, _) =>
        debug("(10) "+cut_occs+ "  ");
        extract(upperProof, cut_occs)
      case _ => throw new Exception("Missing rule in StructCreators.extract: "+p.rule)
    }

    //the original version:
    def handleSchemaProofLink( so: Sequent , name: String, indices: List[IntegerTerm], cut_occs: TypeSynonyms.CutOccurrenceConfiguration) = {
      val schema = SchemaProofDB.get( name )
      val sym = new ClauseSetSymbol( name,
        cutOccConfigToCutConfig( so, cut_occs.filter( occ => (so.antecedent ++ so.succedent).contains(occ)),
                                 schema.seq, schema.vars, indices) )
      val atom = IndexedPredicate( sym, indices )
      A( toOccurrence( atom, so ) )
    }

    // Daniel: I quote gui/prooftool/src/main/scala/at/logic/gui/prooftool/gui/Main.scala:
    // "FixedFOccs does not exist anymore. I don't know what should be the correct parameter for this function."
    // I don't know what the correct code is for the "new version" below, hence I replace it by
    // the "original version" above which does not reference FixedFOccs.

    /*
    //the new version: TODO:remove it!
    def handleSchemaProofLink( so: Sequent , name: String, indices: List[IntegerTerm], cut_occs: TypeSynonyms.CutOccurrenceConfiguration) = {
      val root = SchemaProofDB.get( name ).rec.root
      val root_focc = root.antecedent++root.succedent
      val cutsInPLink = cut_occs.filter( occ => (so.antecedent ++ so.succedent).contains(occ)).map(fo => if(FixedFOccs.PLinksMap.contains(fo)) FixedFOccs.PLinksMap.get(fo).get else fo)
      //println("\ncutsInPLink = "+cutsInPLink)
//      root_focc.filter(fo => getAncestors(fo).intersect(cutsInPLink).nonEmpty)
//      val sym = new ClauseSetSymbol( name, cutOccConfigToCutConfig.applyRCC( so, cut_occs.filter( occ => (so.antecedent ++ so.succedent).contains(occ))))
      val sym = if ((so.antecedent ++ so.succedent).intersect(FixedFOccs.PLinksMap.keySet.toList).nonEmpty)
              new ClauseSetSymbol( name, cutOccConfigToCutConfig.applyRCC( root, cutsInPLink.filter( occ => (root.antecedent ++ root.succedent).contains(occ))))
                else
              new ClauseSetSymbol( name, cutOccConfigToCutConfig.applyRCC( so, cut_occs.filter( occ => (so.antecedent ++ so.succedent).contains(occ))))
      val atom = IndexedPredicate( sym, indices )
      A( toOccurrence( atom, so ) )
    }*/

    def handleLabelledAxiom( lso: LabelledSequent , cut_occs: Set[FormulaOccurrence] ) = {
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
      makeTimesJunction( ant:::suc, Nil )
    }

    def handleAxiom( so: Sequent , cut_occs: Set[FormulaOccurrence] ) = {
      val cutAncInAntecedent = so.antecedent.toList.filter(x => cut_occs.contains(x)).map(x => Dual(A(x)))   //
      val cutAncInSuccedent = so.succedent.toList.filter(x => cut_occs.contains(x)).map(x => A(x))
      makeTimesJunction(cutAncInAntecedent:::cutAncInSuccedent, Nil)
    }

    def handleUnary( upperProof: LKProof, cut_occs: Set[FormulaOccurrence] ) =
      extract(upperProof, cut_occs)

    def handleBinary( upperProofLeft: LKProof, upperProofRight: LKProof, l: List[FormulaOccurrence], cut_occs: Set[FormulaOccurrence] ) = {
      if (cut_occs.contains(l.head))
        Plus(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs))
      else
        Times(extract(upperProofLeft, cut_occs), extract(upperProofRight, cut_occs), l)
    }

    def makeTimesJunction(structs: List[Struct], aux: List[FormulaOccurrence]):Struct = structs match {
      case Nil => EmptyTimesJunction()
      case s1::Nil => s1
      case s1::tail => Times(s1, makeTimesJunction(tail, aux), aux)
    }
  }


  //returns an arithmetically ground struct
  object groundStruct {
    def apply(s: Struct, subst: HOLSubstitution) : Struct = {
      s match {
        case A(fo) => {
          fo.formula match {
            case IndexedPredicate(f,l) => f.sym match {
              case clsym: ClauseSetSymbol => {
                return A(fo.factory.createFormulaOccurrence(subst(fo.formula), Nil))
              }
              case _ => {}
            }
            case _ => {}
          }
          A(fo.factory.createFormulaOccurrence(subst(fo.formula), Nil)) // ????????????????????????
        }
        case Dual(sub) => Dual(apply(sub, subst))
        case Times(left, right, foList) => Times(apply(left, subst), apply(right, subst), foList.map(fo => fo.factory.createFormulaOccurrence(subst(fo.formula).asInstanceOf[HOLFormula], Nil)))
        case Plus(left, right) => Plus(apply(left, subst), apply(right, subst))
        case _ => s
      }
    }
  }


  //unfolds an arithmetically ground struct
  object unfoldGroundStruct {
    def apply(s: Struct) : Struct = {
      s match {
        case A(fo) => {
          fo.formula match {
            case HOLApp(f,l) => f.asInstanceOf[HOLConst].sym match {
              case clsym: ClauseSetSymbol => {
                if(l == IntZero()) {
                  val base = SchemaProofDB.get(clsym.name).base
                  //TODO: take into account the omega-ancestors
                  return StructCreators.extract(base, getCutAncestors(base))
                }
                //println("clsym = ("+clsym.name+","+l+")")
                val step = SchemaProofDB.get(clsym.name).rec
                //TODO: take into account the omega-ancestors
                val struct = StructCreators.extract(step, getCutAncestors(step))
                //println("struct : "+struct)
                val new_map = Map.empty[SchemaVar, IntegerTerm] + Tuple2(IntVar("k"), Pred(l.asInstanceOf[IntegerTerm]))
                val new_subst = SchemaSubstitution(new_map)
                val gr_struct = groundStruct(struct, new_subst.asInstanceOf[HOLSubstitution])
                //println("ground struct : "+gr_struct)
                return unfoldGroundStruct(gr_struct)
              }
              case _ => {
                //if(f.asInstanceOf[HOLConst].name.toString().contains("cl^"))
                  //println("proof_name = "+f.asInstanceOf[HOLConst].name.asInstanceOf[ClauseSetSymbol].name)
              }
            }
            case _ => ()//println("complex f-la")
          }
          A(fo.factory.createFormulaOccurrence(fo.formula, Nil))
        }
        case Dual(sub) => Dual(apply(sub))
        case Times(left, right, foList) => Times(apply(left), apply(right), foList.map(fo => fo.factory.createFormulaOccurrence(fo.formula, Nil)))
        case Plus(left, right) => Plus(apply(left), apply(right))
        case _ => s
      }
    }
  }



