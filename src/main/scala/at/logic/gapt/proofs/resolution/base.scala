/*
 * base.scala
 *
 */

package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol.TypeSynonyms.SkolemSymbol
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.proofs.lk.base.{ Sequent, FSequent, createContext => lkCreateContext }
import at.logic.gapt.proofs.lksk.LabelledFormulaOccurrence
import at.logic.gapt.proofs.lksk.TypeSynonyms.Label
import at.logic.gapt.expr.hol._
import at.logic.gapt.expr._
import at.logic.gapt.expr.{ TA, FunctionType }
import at.logic.gapt.utils.ds.acyclicGraphs._

trait ResolutionProof[V <: Sequent] extends AGraphProof[V]

trait NullaryResolutionProof[V <: Sequent] extends NullaryAGraphProof[V] with ResolutionProof[V] with NullaryProof[V]
trait UnaryResolutionProof[V <: Sequent] extends UnaryAGraphProof[V] with ResolutionProof[V] with UnaryProof[V] {
  override def uProof = t.asInstanceOf[ResolutionProof[V]]
}
trait BinaryResolutionProof[V <: Sequent] extends BinaryAGraphProof[V] with ResolutionProof[V] with BinaryProof[V] {
  override def uProof1 = t1.asInstanceOf[ResolutionProof[V]]
  override def uProof2 = t2.asInstanceOf[ResolutionProof[V]]
}

// FIXME: this should not be called 'CNF'. It does not describe a CNF but a clause.
trait CNF extends Sequent {
  require( ( antecedent ++ succedent ).forall( x =>
    x.formula match {
      case HOLAtom( _, _ ) => true;
      case _               => false
    } ) )
}

/**
 * the sequences are actually multisets, as can be seen from the equal method
 */
// TODO: make a class out of this?? (That extends sequent, maybe) I did not manage to reuse it where I wanted... 
// Too many castings and adaptations had to be done (seqs to sets or lists, Formulas to FOLFormulas, etc) :(
trait FClause {
  def neg: Seq[HOLFormula]
  def pos: Seq[HOLFormula]
  def multisetEquals( f: FClause, g: FClause ): Boolean =
    f.neg.diff( g.neg ).isEmpty && f.pos.diff( g.pos ).isEmpty &&
      g.neg.diff( f.neg ).isEmpty && g.pos.diff( f.pos ).isEmpty

  override def equals( o: Any ) = o match {
    case s: FClause => multisetEquals( this, s )
    case _          => false
  }
  override def hashCode = neg.map( _.hashCode ).sum + 31 * pos.map( _.hashCode ).sum
  override def toString = {
    var sb = new scala.StringBuilder()
    var first = true
    for ( f <- neg ) {
      if ( !first ) sb.append( ", " )
      else first = false

      sb.append( f )
    }
    sb.append( " :- " )
    first = true
    for ( f <- pos ) {
      if ( !first ) sb.append( ", " )
      else first = false
      sb.append( f )

    }
    sb.toString
  }

  def isSubClauseOf( c: FClause ) = neg.diff( c.neg ).isEmpty && pos.diff( c.pos ).isEmpty

  def toFSequent = FSequent( neg.map( _.asInstanceOf[HOLFormula] ), pos.map( _.asInstanceOf[HOLFormula] ) )

  /*
   compose constructs a sequent from two sequents. Corresponds to the 'o' operator in CERes
   should be moved to FSequent once FSequent is called Sequent (see Issue 201)
  */
  def compose( other: FClause ) = new FClause { def neg = FClause.this.neg ++ other.neg; def pos = FClause.this.pos ++ other.pos }
}

// a default factory
object FClause {
  def apply( n: Seq[HOLFormula], p: Seq[HOLFormula] ): FClause = new FClause { def neg = n; def pos = p }
  def unapply( fc: FClause ) = Some( ( fc.neg, fc.pos ) )
}

// the boolean represent isPositive as the negation is stripped from the literals
class Clause( val literals: Seq[Tuple2[FormulaOccurrence, Boolean]] ) extends Sequent(
  literals.filter( !_._2 ).map( _._1 ),
  literals.filter( _._2 ).map( _._1 ) ) with CNF {
  def negative = antecedent
  def positive = succedent
  def toFClause = FClause( negative.map( _.formula ), positive.map( _.formula ) )
}

object Clause {
  def apply( literals: Seq[Tuple2[FormulaOccurrence, Boolean]] ) = new Clause( literals )
  def apply( neg: Seq[FormulaOccurrence], pos: Seq[FormulaOccurrence] ) = new Clause( neg.map( ( _, false ) ) ++ pos.map( ( _, true ) ) )
  def unapply( s: Sequent ) = s match {
    case c: Clause => Some( c.negative, c.positive )
    case _         => None
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
  def apply[V <: Sequent]( ant: Seq[HOLFormula], suc: Seq[HOLFormula] )( implicit factory: FOFactory ) = {
    val left: Seq[FormulaOccurrence] = ant.map( factory.createFormulaOccurrence( _, Nil ) )
    val right: Seq[FormulaOccurrence] = suc.map( factory.createFormulaOccurrence( _, Nil ) )
    new LeafAGraph[Sequent]( Sequent( left, right ) ) with NullaryResolutionProof[V] { def rule = InitialType }
  }

  def unapply[V <: Sequent]( proof: ResolutionProof[V] ) = if ( proof.rule == InitialType ) Some( ( proof.root ) ) else None
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
  def apply[V <: Sequent]( p: ResolutionProof[V] ): Set[V] =
    p.nodes.collect {
      case n: NullaryResolutionProof[V] if n.rule == InitialType => n.root
    }
}

