/*
 * base.scala
 *
 */

package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol.TypeSynonyms.SkolemSymbol
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.proofs.lk.base.{ createContext => lkCreateContext, Sequent, OccSequent, HOLSequent }
import at.logic.gapt.proofs.lksk.LabelledFormulaOccurrence
import at.logic.gapt.proofs.lksk.TypeSynonyms.Label
import at.logic.gapt.expr.hol._
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

object Clause {
  def apply[A](): Clause[A] = new Clause( Seq(), Seq() )
  def apply[A]( negative: Seq[A], positive: Seq[A] ) = new Clause( negative, positive )
  def apply[A]( elements: Seq[( A, Boolean )] ) = new Clause( elements.filterNot( _._2 ).map( _._1 ), elements.filter( _._2 ).map( _._1 ) )

  def unapply[A]( clause: Clause[A] ) = Some( ( clause.negative, clause.positive ) )
}

object HOLClause {
  def apply(): HOLClause = Clause()

  def apply( negative: Seq[HOLAtom], positive: Seq[HOLAtom] ): HOLClause = {
    Clause( negative, positive )
  }

  def apply( negative: Seq[HOLFormula], positive: Seq[HOLFormula] )( implicit dummyImplicit: DummyImplicit ): HOLClause = {
    HOLClause( negative map { _.asInstanceOf[FOLAtom] }, positive map { _.asInstanceOf[FOLAtom] } )
  }

  def apply( elements: Seq[( HOLAtom, Boolean )] ): HOLClause = {
    Clause( elements )
  }

  def unapply( clause: HOLClause ) = Some( clause.toTuple )
}

object FOLClause {
  def apply(): FOLClause = Clause()

  def apply( negative: Seq[FOLAtom], positive: Seq[FOLAtom] ): FOLClause = {
    Clause( negative, positive )
  }

  def apply( negative: Seq[FOLFormula], positive: Seq[FOLFormula] )( implicit dummyImplicit: DummyImplicit ): FOLClause = {
    FOLClause( negative map { _.asInstanceOf[FOLAtom] }, positive map { _.asInstanceOf[FOLAtom] } )
  }

  def apply( elements: Seq[( FOLAtom, Boolean )] ): FOLClause = {
    Clause( elements )
  }

  def CNFtoFormula( cls: List[FOLClause] ): FOLFormula =
    {
      val nonEmptyClauses = cls.filter( c => c.negative.length > 0 || c.positive.length > 0 ).toList

      if ( nonEmptyClauses.length == 0 ) { Top() }
      else { And( nonEmptyClauses.map( c => Or( c.positive ++ c.negative.map( l => Neg( l ) ) ) ) ) }
    }

  //FIXME: Maybe find a better place for this
  def NumberedCNFtoFormula( cls: List[Clause[( FOLAtom, Int )]] ) = CNFtoFormula( cls map { c => c map { p => p._1 } } )

  def unapply( clause: FOLClause ) = Some( clause.toTuple )
}

object OccClause {
  def apply( negative: Seq[FormulaOccurrence], positive: Seq[FormulaOccurrence] ): OccClause = {
    require( ( negative ++ positive ).map( _.formula ) forall {
      case HOLAtom( _ ) => true
      case _            => false
    } )

    Clause( negative, positive )
  }

  def apply( elements: Seq[( FormulaOccurrence, Boolean )] ): OccClause = {
    require( ( elements map { p => p._1.formula } ) forall {
      case HOLAtom( _ ) => true
      case _            => false
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

  // used in ral
  def apply( sk: SkolemSymbol, t: TA, label: Label ) = {
    val tp = FunctionType( t, label.toList.map( v => v.exptype ) )
    HOLFunction( Const( sk, tp ), label.toList )
  }
}

object initialSequents {
  def apply[V <: OccSequent]( p: ResolutionProof[V] ): Set[V] =
    p.nodes.collect {
      case n: NullaryResolutionProof[V] if n.rule == InitialType => n.root
    }
}

