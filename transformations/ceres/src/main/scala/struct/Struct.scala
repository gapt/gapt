/*
 * Struct.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.ceres

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkExtractors._
import at.logic.calculi.lksk.lkskExtractors._
import at.logic.calculi.lksk.base._
import at.logic.algorithms.lk.getCutAncestors
import at.logic.utils.ds.trees._
import at.logic.language.lambda.types.ImplicitConverters._

// imports for schema stuff
import at.logic.calculi.slk._
import at.logic.language.schema._
import at.logic.language.lambda.symbols._
import at.logic.utils.ds.Multisets._

import scala.collection.immutable.Set

package struct {
  trait Struct extends Tree[HOLExpression]

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

  // The times operator stores the auxiliary formulas of the 
  // inference which induces it.
  case class Times(left: Struct, right: Struct, auxFOccs: List[FormulaOccurrence]) extends BinaryTree[HOLExpression](TimesC, left, right) with Struct
  case class Plus(left: Struct, right: Struct) extends BinaryTree[HOLExpression](PlusC, left, right) with Struct
  case class Dual(sub: Struct) extends UnaryTree[HOLExpression](DualC, sub) with Struct
  case class A(formula: FormulaOccurrence) extends LeafTree[HOLExpression](formula.formula) with Struct // Atomic Struct
  case class EmptyTimesJunction() extends LeafTree[HOLExpression](EmptyTimesC) with Struct
  case class EmptyPlusJunction() extends LeafTree[HOLExpression](EmptyPlusC) with Struct

  // In the construction of schematized clause sets, we use symbols
  // that contain a name and a cut-configuration. This class represents
  // such symbols.
  class ClauseSetSymbol(val name: String, val cut_occs: Multiset[SchemaFormula]) extends ConstantSymbolA {
    def compare( that: SymbolA ) : Int =
      // TODO: implement
      throw new Exception

    def toCode() : String =
      // TODO: implement
      throw new Exception
  }

  object StructCreators {

    def extract(p: LKProof) : Struct = extract( p, getCutAncestors( p ) )

    def extract(p: LKProof, cut_occs: Set[FormulaOccurrence]):Struct = p match {
      case Axiom(so) => // in case of axioms of the form A :- A with labelled formulas, proceed as in Daniel's PhD thesis
      so match {
        case lso : LabelledSequentOccurrence if lso.l_antecedent.size == 1 && lso.l_succedent.size == 1 =>
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

    def handleSchemaProofLink( so: SequentOccurrence, name: String, indices: List[IntegerTerm], cut_occs: Set[FormulaOccurrence]) = {
      val sym = new ClauseSetSymbol( name, cut_occs.foldLeft(HashMultiset[SchemaFormula])( (s,o) => s + o.formula.asInstanceOf[SchemaFormula] ) )
      val atom = IndexedPredicate( sym, indices )
      val others = so.antecedent ++ so.succedent
      A( others.head.factory.createPrincipalFormulaOccurrence(atom, Nil, others) )
    }

    def handleLabelledAxiom( lso: LabelledSequentOccurrence, cut_occs: Set[FormulaOccurrence] ) = {
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

    def handleAxiom( so: SequentOccurrence, cut_occs: Set[FormulaOccurrence] ) = {
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
