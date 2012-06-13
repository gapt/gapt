/*
 * Struct.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.ceres

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.hol.{HOLConst, HOLFormula,HOLExpression}
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lksk.lkskExtractors._
import at.logic.calculi.lksk.base._
import at.logic.algorithms.lk.{getAncestors, getCutAncestors}
import at.logic.utils.ds.trees._
import at.logic.language.lambda.types.ImplicitConverters._

// imports for schema stuff
import at.logic.calculi.slk._
import at.logic.language.schema._
import at.logic.language.lambda.symbols._
import at.logic.utils.ds.Multisets._

import scala.collection.immutable.{HashSet, Set}
import at.logic.calculi.lk.base.types.FSequent

// for debugging
import clauseSets.StandardClauseSet._

package struct {

trait Struct

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

  class Times(val left: Struct, val right: Struct, val auxFOccs: List[FormulaOccurrence]) extends Struct
  case class Plus(left: Struct, right: Struct) extends Struct
  case class Dual(sub: Struct) extends Struct
  case class A(formula: FormulaOccurrence) extends Struct // Atomic Struct
  case class EmptyTimesJunction() extends Struct
  case class EmptyPlusJunction() extends Struct

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

    case object TimesSymbol extends LogicalSymbolsA {
      override def unique = "TimesSymbol"
      override def toString = "⊗"
      def toCode = "TimesSymbol"
    }

    case object PlusSymbol extends LogicalSymbolsA {
      override def unique = "PlusSymbol"
      override def toString = "⊕"
      def toCode = "PlusSymbol"
    }

    case object DualSymbol extends LogicalSymbolsA {
      override def unique = "DualSymbol"
      override def toString = "∼"
      def toCode = "DualSymbol"
    }

    case object EmptyTimesSymbol extends LogicalSymbolsA {
      override def unique = "EmptyTimesSymbol"
      override def toString = "ε_⊗"
      def toCode = "EmptyTimesSymbol"
    }

    case object EmptyPlusSymbol extends LogicalSymbolsA {
      override def unique = "EmptyPlusSymbol"
      override def toString = "ε_⊕"
      def toCode = "EmptyPlusSymbol"
    }

    case object TimesC extends HOLConst(TimesSymbol, "( o -> (o -> o) )")
    case object PlusC extends HOLConst(PlusSymbol, "( o -> (o -> o) )")
    case object DualC extends HOLConst(DualSymbol, "(o -> o)")
    case object EmptyTimesC extends HOLConst(EmptyTimesSymbol, "o")
    case object EmptyPlusC extends HOLConst(EmptyPlusSymbol, "o")
  }

  // some stuff for schemata

  // cut configurations: one using multisets of formulas (to relate different proof definitions)
  // and one using FormulaOccurrences (if we are only considering a single proof definition)
  object TypeSynonyms {
    type CutConfiguration = (Multiset[SchemaFormula], Multiset[SchemaFormula])
    type CutOccurrenceConfiguration = Set[FormulaOccurrence]
  }

  import TypeSynonyms._

  // Takes a CutOccurrenceConfiguration and creates a CutConfiguration cc
  // by, for each o in cc, taking the element f from seq such that
  // f, where param goes to term, is equal to o.formula.
  object cutOccConfigToCutConfig {
    def apply( so: Sequent, cc: CutOccurrenceConfiguration, seq: FSequent, params: List[IntVar], terms: List[IntegerTerm]) =
      cc.foldLeft( (HashMultiset[SchemaFormula](), HashMultiset[SchemaFormula]() ) )( (res, fo) => {
        val cca = res._1
        val ccs = res._2
        if (so.antecedent.contains( fo ))
          (cca + getFormulaForCC( fo, seq._1.asInstanceOf[List[SchemaFormula]], params, terms ), ccs)
        else if (so.succedent.contains( fo ))
          (cca, ccs + getFormulaForCC( fo, seq._2.asInstanceOf[List[SchemaFormula]], params, terms ))
        else
          throw new Exception
      })

    def getFormulaForCC( fo: FormulaOccurrence, fs: List[SchemaFormula], params: List[IntVar], terms: List[IntegerTerm] ) =
    {
      //println("in getFormulaForCC")
      //println("fo.formula = " + fo.formula)
      val sub = Substitution[SchemaExpression](params.zip(terms))
      //println("sub = " + sub)
      val list = fs.filter( f => {
        //println("f = " + f )
        //println( "sub(f) = " + sub(f) )
        //println( sub(f) == fo.formula )
        sub(f) == fo.formula
      }) 
      //println("list.size = " + list.size)
      list match {
        case Nil => {
          //println("list is Nil!?")
          //println(list)
          throw new Exception("Could not find a formula to construct the cut-configuration!")
        }
        case x::_ => x
      }
    }
  }

  // In the construction of schematized clause sets, we use symbols
  // that contain a name and a cut-configuration. This class represents
  // such symbols.
  class ClauseSetSymbol(val name: String, val cut_occs: CutConfiguration) extends ConstantSymbolA {
    def compare( that: SymbolA ) : Int =
      // TODO: implement
      throw new Exception

    def toCode() : String =
      // TODO: implement
      throw new Exception

    override def toString() =
      "CL^{(" + cutConfToString(cut_occs) + ")," + name +"}"

    private def cutConfToString( cc : CutConfiguration ) = {
      def str( m : Multiset[SchemaFormula] ) = m.foldLeft( "" )( (s, f) => s + f.toStringSimple )
      str( cc._1 ) + "|" + str( cc._2 )
    }
  }

  object StructCreators {

    // this is for proof schemata: it extracts the characteristic
    // clause set for the proof called "name"
    // fresh_param should be fresh

    def extractFormula(name: String, fresh_param: IntVar) : SchemaFormula =
    {
      val cs_0_f = SchemaProofDB.foldLeft[SchemaFormula](TopC)((f, ps) => 
        And(cutConfigurations( ps._2.base ).foldLeft[SchemaFormula](TopC)((f2, cc) =>
          And(Imp(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.base.root, cc, ps._2.seq, ps._2.vars, IntZero()::Nil ) ), 
                                   IntZero()::Nil ),
                  toFormula(extractBaseWithCutConfig(ps._2, cc))), f2)),
            f) )

      // assumption: all proofs in the SchemaProofDB have the
      // same running variable "k".
      val k = IntVar(new VariableStringSymbol("k") )
      val cs_1_f = SchemaProofDB.foldLeft[SchemaFormula](TopC)((f, ps) => 
        And(cutConfigurations( ps._2.rec ).foldLeft[SchemaFormula](TopC)((f2, cc) => 
          And(Imp(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.rec.root, cc, ps._2.seq, ps._2.vars, Succ(k)::Nil ) ), 
                                   Succ(k)::Nil ),
                  toFormula(extractStepWithCutConfig(ps._2, cc))), f2)
              ),
            f) )

      val cl_n = IndexedPredicate( new ClauseSetSymbol(name, (HashMultiset[SchemaFormula], HashMultiset[SchemaFormula]) ), 
                                   fresh_param::Nil )
      And(cl_n, And( cs_0_f , BigAnd( k, cs_1_f, IntZero(), fresh_param )))
    }

    def toFormula(s: Struct) : SchemaFormula =
      transformStructToClauseSet( s ).foldLeft[SchemaFormula](TopC)((f, c) => 
        And(f, toFormula(c)))

    // FIXME: this method should not exist.
    // it's a workaround necessary since so far, the logical
    // constants are not created by the factories, and hence
    // do not work across language-levels, but the constants
    // are neede to transform a sequent to a formula in general.
    def toFormula( s: Sequent ) : SchemaFormula =
      Or( s.antecedent.map( f => Neg( f.formula.asInstanceOf[SchemaFormula] )).toList ++ (s.succedent map (_.formula.asInstanceOf[SchemaFormula])) )

    def extractStruct(name: String, fresh_param: IntVar) : Struct =
    {
      val cs_0 = SchemaProofDB.foldLeft[Struct](EmptyPlusJunction())((s, ps) => 
        Plus(cutConfigurations( ps._2.base ).foldLeft[Struct](EmptyPlusJunction())((s2, cc) =>
          Plus(Times(Dual(A(toOccurrence(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.base.root, cc, ps._2.seq, ps._2.vars, IntZero()::Nil ) ), IntZero()::Nil ), ps._2.base.root ) ) ), extractBaseWithCutConfig(ps._2, cc)), s2)),
            s) )

      // assumption: all proofs in the SchemaProofDB have the
      // same running variable "k".
      val k = IntVar(new VariableStringSymbol("k") )
      val schema = SchemaProofDB.get( name )
      val precond = Times(A(toOccurrence(BiggerThan(IntZero(),k), schema.rec.root)),
                          A(toOccurrence(BiggerThan(k, fresh_param), schema.rec.root)))
      val cs_1 = Times(precond, SchemaProofDB.foldLeft[Struct](EmptyPlusJunction())((s, ps) => 
        Plus(cutConfigurations( ps._2.rec ).foldLeft[Struct](EmptyPlusJunction())((s2, cc) => 
          Plus(Times(Dual(A(toOccurrence(IndexedPredicate( new ClauseSetSymbol( ps._2.name, cutOccConfigToCutConfig( ps._2.rec.root, cc, ps._2.seq, ps._2.vars, Succ(k)::Nil ) ), Succ(k)::Nil ), ps._2.rec.root ) ) ), extractStepWithCutConfig(ps._2, cc), Nil), s2)
              ),
            s) ))

      val cl_n = IndexedPredicate( new ClauseSetSymbol(name, (HashMultiset[SchemaFormula], HashMultiset[SchemaFormula]) ), 
                                   fresh_param::Nil )
      Plus(A(toOccurrence(cl_n, schema.rec.root)), Plus( cs_0 ,cs_1) )
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

////    computes relevant cut configurations
//    def cutConfigurations( p: LKProof ) : Set[Set[FormulaOccurrence]] = {
//      all(name).get(p)
//    }
//
//    def all(proof_name:String) = createMapFromLKProoftoSetOfFOccs(RelevantCC(proof_name))
    
    def extractStepWithCutConfig( schema: SchemaProof, cc: CutOccurrenceConfiguration ) =
    {
      extract( schema.rec, getAncestors( cc ) ++ getCutAncestors( schema.rec ) )
    }
/*
    def extractSteps(fresh_param: IntVar) = {
      println("extracting step clause sets")

      // compute for the step case (i.e. CS_1)
      SchemaProofDB.foldLeft[Struct]( EmptyPlusJunction() ) ( (struct, ps) => {
        val n = ps._1
        val schema = ps._2
        println("computing cut configurations")
        val ccs = cutConfigurations( schema.rec )
        println("computing cut ancestors")
        val cut_ancs = getCutAncestors( schema.rec )
        println("first compute for proof " + n)
        // TODO: due to schema.vars.head in the next line, we only support
        // proofs with a single integer parameter. To support more,
        // the definition of ClauseSetSymbol needs to be extended.
        val k = schema.vars.head

        Times( precond, Plus( struct, ccs.foldLeft[Struct]( EmptyPlusJunction() )( (struct2, cc) =>
        {
          println("cut configuration: " + cc)
          val pred = IndexedPredicate( new ClauseSetSymbol( n, cutOccConfigToCutConfig( schema.rec.root, cc ) ), Succ(k)::Nil )
          Plus(struct2, Times(Dual(A(toOccurrence(pred, schema.rec.root))), extractStepWithCutConfig(schema, cc), Nil ))
        }), Nil))
      })
    }
*/
    def extractBaseWithCutConfig( schema: SchemaProof, cc: CutOccurrenceConfiguration ) =
    {
      extract( schema.base, getAncestors( cc ) ++ getCutAncestors( schema.base ) )
    }
/*
    def extractBases : Struct = {
      println("extracting base clause sets")

      // create the set of all possible cut-configurations
      // for p
      /*
      def toFormulaMultiset( s: Set[FormulaOccurrence] ) = s.foldLeft( HashMultiset() )( (res, o) => res + o.formula )
      def cutConfigurations( s: Set[FormulaOccurrence] ) = combinations( s.size, toMultiset( s ) )
      def cutConfigurations( p: LKProof ) = {
        val ca = cutConfigurations( p.root.antecedent )
        val cs = cutConfigurations( p.root.succedent )
        ca.foldLeft( new HashSet[CutConfiguration] )( (res, cc) =>
          res ++ cs.foldLeft( new HashSet[CutConfiguration] )( (res2, cc2) => res2 + (cc, cc2) ) )
      } */


      // compute for base case (i.e. CS_0)
      SchemaProofDB.foldLeft[Struct]( EmptyPlusJunction() )( (struct, ps) => {
        val n = ps._1
        val schema = ps._2
        val ccs = cutConfigurations( schema.base )
        val cut_ancs = getCutAncestors( schema.base )
        //println("first compute for proof " + n)
        val res = Plus(struct, ccs.foldLeft[Struct]( EmptyPlusJunction() )( (struct2, cc) =>
        {
          //println("cut configuration: " + cc)
          val pred = IndexedPredicate( new ClauseSetSymbol( n, cutOccConfigToCutConfig( schema.base.root, cc ) ), IntZero()::Nil )
          val res = Times(Dual(A(toOccurrence(pred, schema.base.root))), extractBaseWithCutConfig( schema, cc ), Nil )
          //println("obtained struct from cc: " + transformStructToClauseSet(res))
          Plus(struct2, res)
        }))
        //println("obtained struct from base case:" + transformStructToClauseSet(res ))
        res
      })
    }
*/
    def toOccurrence( f: HOLFormula, so: Sequent ) =
    {
//      val others = so.antecedent ++ so.succedent
//      others.head.factory.createPrincipalFormulaOccurrence(f, Nil, others)
      defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, Nil)
    }

    def extract(p: LKProof) : Struct = extract( p, getCutAncestors( p ) )
    def extract(p: LKProof, predicate: HOLFormula => Boolean) : Struct = extract( p, getCutAncestors( p, predicate ) )

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
      so match {
        case lso : LabelledSequent  if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 =>
          handleLabelledAxiom( lso, cut_occs )
        case _ => handleAxiom( so, cut_occs )
      }
      case UnaryLKProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
      case BinaryLKProof(_, upperProofLeft, upperProofRight, _, aux1, aux2, _) => 
        handleBinary( upperProofLeft, upperProofRight, aux1::aux2::Nil, cut_occs )
      case UnaryLKskProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
      case UnarySchemaProof(_,upperProof,_,_,_) => handleUnary( upperProof, cut_occs )
      case SchemaProofLinkRule(so, name, indices) => handleSchemaProofLink( so, name, indices, cut_occs )
    }

    def handleSchemaProofLink( so: Sequent , name: String, indices: List[IntegerTerm], cut_occs: CutOccurrenceConfiguration) = {
      val schema = SchemaProofDB.get( name )
      val sym = new ClauseSetSymbol( name,
        cutOccConfigToCutConfig( so, cut_occs.filter( occ => (so.antecedent ++ so.succedent).contains(occ)),
                                 schema.seq, schema.vars, indices) )
      val atom = IndexedPredicate( sym, indices )
      A( toOccurrence( atom, so ) )
    }

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
//      case s1::tail => new Times() with Labeled {type T = LKProof, def label: LKProof =  }
    }
  }
}
