/*
 * base.scala
 *
 */

package at.logic.gapt.proofs.resolutionOld

import at.logic.gapt.expr.hol.TypeSynonyms.SkolemSymbol
import at.logic.gapt.proofs.Clause
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.proofs.lk.base.{ createContext => lkCreateContext, OccSequent }
import at.logic.gapt.proofs.lksk.LabelledFormulaOccurrence
import at.logic.gapt.expr._
import at.logic.gapt.expr.{ TA, FunctionType }
import at.logic.gapt.utils.ds.acyclicGraphs._

trait ResolutionProof[V <: OccSequent] extends AGraphProof[V]

trait NullaryResolutionProof[V <: OccSequent] extends NullaryAGraphProof[V] with ResolutionProof[V] with NullaryProof[V]
trait UnaryResolutionProof[V <: OccSequent] extends UnaryAGraphProof[V] with ResolutionProof[V] with UnaryProof[V] {
  override def uProof = t.asInstanceOf[ResolutionProof[V]]
}
trait BinaryResolutionProof[V <: OccSequent] extends BinaryAGraphProof[V] with ResolutionProof[V] with BinaryProof[V] {
  override def uProof1 = t1.asInstanceOf[ResolutionProof[V]]
  override def uProof2 = t2.asInstanceOf[ResolutionProof[V]]
}

object OccClause {
  def apply( negative: Seq[FormulaOccurrence], positive: Seq[FormulaOccurrence] ): OccClause = {
    require( ( negative ++ positive ).map( _.formula ) forall {
      case HOLAtom( _, _ ) => true
      case _               => false
    } )

    Clause( negative, positive )
  }

  def apply( elements: Seq[( FormulaOccurrence, Boolean )] ): OccClause = {
    require( ( elements map { p => p._1.formula } ) forall {
      case HOLAtom( _, _ ) => true
      case _               => false
    } )

    Clause( elements )
  }
}

trait InstantiatedVariable {
  def term: LambdaExpression
}
trait AppliedSubstitution {
  def substitution: Substitution
}

case object InitialType extends NullaryRuleTypeA

object InitialSequent {
  def apply[V <: OccSequent]( ant: Seq[HOLFormula], suc: Seq[HOLFormula] )( implicit factory: FOFactory ) = {
    val left: Seq[FormulaOccurrence] = ant.map( factory.createFormulaOccurrence( _, Nil ) )
    val right: Seq[FormulaOccurrence] = suc.map( factory.createFormulaOccurrence( _, Nil ) )
    new LeafAGraph[OccSequent]( OccSequent( left, right ) ) with NullaryResolutionProof[V] { def rule = InitialType }
  }

  def unapply[V <: OccSequent]( proof: ResolutionProof[V] ) = if ( proof.rule == InitialType ) Some( ( proof.root ) ) else None
  // should be optimized as it was done now just to save coding time
}

// exceptions
class ResolutionRuleException( msg: String ) extends RuleException( msg )
class ResolutionRuleCreationException( msg: String ) extends ResolutionRuleException( msg )

// Functions used by all files.

object createContext {
  // creates new formula occurrences where sub is applied to each element x in the given set and which has x as an ancestor
  // additional_context  may add additional ancestors, needed e.g. for factoring
  // used in Robinson
  def apply( set: Seq[FormulaOccurrence], sub: Substitution ): Seq[FormulaOccurrence] =
    apply( set, sub, Map[FormulaOccurrence, List[FormulaOccurrence]]() )
  def apply( set: Seq[FormulaOccurrence], sub: Substitution, additional_context: Map[FormulaOccurrence, Seq[FormulaOccurrence]] ): Seq[FormulaOccurrence] =
    set.map( x =>
      x.factory.createFormulaOccurrence( sub( x.formula ), x :: additional_context.getOrElse( x, Nil ).toList ) )

  // used in Andrews and Ral
  def apply( seq: Seq[FormulaOccurrence] ): Seq[LabelledFormulaOccurrence] = lkCreateContext( seq ).asInstanceOf[Seq[LabelledFormulaOccurrence]]
}

object computeSkolemTerm {
  // used in andrews
  def apply( sk: SkolemSymbol, t: TA, sub: LambdaExpression ) = {
    val fv = freeVariables( sub ).toList
    val tp = FunctionType( t, fv.map( v => v.exptype ) )
    HOLFunction( Const( sk, tp ), fv )
  }
}

object initialSequents {
  def apply[V <: OccSequent]( p: ResolutionProof[V] ): Set[V] =
    p.nodes.collect {
      case n: NullaryResolutionProof[V] if n.rule == InitialType => n.root
    }
}

