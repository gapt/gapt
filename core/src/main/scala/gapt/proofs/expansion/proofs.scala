package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.hol.SkolemFunctions
import gapt.formats.babel.BabelSignature
import gapt.proofs.context.Context
import gapt.proofs.{ Checkable, HOLSequent, Sequent }
import gapt.utils.linearizeStrictPartialOrder

import scala.collection.mutable

/**
 * Expansion proof.
 *
 * An expansion proof consists of a sequent of expansion trees without
 * duplicate eigenvariable where the dependency relation of the eigenvariables is acyclic.
 */
case class ExpansionProof( expansionSequent: Sequent[ExpansionTree] ) {
  for ( ( tree, index ) <- expansionSequent.zipWithIndex )
    require( tree.polarity == index.polarity, s"Wrong polarity, ${index.polarity} expected:\n$tree" )

  val eigenVariables: Set[Var] = {
    val evs = mutable.Set[Var]()
    val fvs = freeVariables( shallow )
    expansionSequent.foreach { tree =>
      tree.term.foreach {
        case ETtStrong( ev, _ ) =>
          require( !evs.contains( ev ), s"duplicate eigenvariable $ev" )
          require( !fvs.contains( ev ), s"eigenvariable $ev is free in shallow sequent" )
          evs += ev
        case _ =>
      }
    }
    evs.toSet
  }
  val dependencyRelation: Set[( Var, Var )] =
    ExpansionProof.dependencies( expansionSequent ).
      filter { case ( a, b ) => eigenVariables( a ) && eigenVariables( b ) }
  val Right( linearizedDependencyRelation ) = linearizeStrictPartialOrder( eigenVariables, dependencyRelation )

  def skolemFunctions: SkolemFunctions = SkolemFunctions(
    subTerms.collect { case ETtSkolem( Apps( skC: Const, _ ), skDef, _ ) => skC -> skDef } )

  def subProofs: Set[ExpansionTree] = expansionSequent.elements.view.flatMap( _.subProofs ).toSet
  def shallow: HOLSequent = expansionSequent.map( _.shallow )
  def deep: HOLSequent = expansionSequent.map( _.deep )
  def termSequent: Sequent[ETt] = expansionSequent.map( _.term )

  def subTerms: Set[ETt] = {
    val result = Set.newBuilder[ETt]
    for ( et <- expansionSequent; st <- et.term ) result += st
    result.result()
  }

  def size: Int = {
    var result = 0
    for ( et <- expansionSequent; _ <- et.term ) result += 1
    result
  }

  def cuts: Vector[ETCut.Cut] =
    expansionSequent.antecedent.flatMap { case ETCut( cuts ) => cuts case _ => Seq() }
  def isCutFree: Boolean = cuts.isEmpty
  def inductions( implicit ctx: Context ): Vector[ETInduction.Induction] =
    expansionSequent.antecedent.flatMap { case ETInduction( inductions ) => inductions case _ => Seq() }
  def nonCutPart: ExpansionSequent = expansionSequent.filterNot( ETCut.isCutExpansion )
  def nonTheoryPart( implicit ctx: Context ): ExpansionSequent =
    expansionSequent.filterNot( et => ETCut.isCutExpansion( et ) || ETInduction.isInductionAxiomExpansion( et ) )
  def theoryPart( implicit ctx: Context ): ExpansionSequent =
    expansionSequent.filter( et => ETCut.isCutExpansion( et ) || ETInduction.isInductionAxiomExpansion( et ) )

  override def toString: String = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ): String =
    expansionSequent.map( _.toSigRelativeString ).toString
}

object ExpansionProof {
  /** Computes the dependency relation of an expansion proof. */
  def dependencies( es: Sequent[ExpansionTree] ): Set[( Var, Var )] = {
    val out = mutable.Set[( Var, Var )]()
    def go( et: ETt, below: Set[Var] ): Unit =
      et match {
        case ETtAtom | ETtNullary | ETtWeakening =>
        case ETtMerge( child1, child2 ) =>
          go( child1, below )
          go( child2, below )
        case ETtUnary( child ) =>
          go( child, below )
        case ETtBinary( child1, child2 ) =>
          go( child1, below )
          go( child2, below )
        case ETtWeak( instances ) =>
          for ( ( inst, ch ) <- instances )
            go( ch, below ++ freeVariables( inst ) )
        case ETtStrong( eigenVar, child ) =>
          for ( b <- below ) out += ( b -> eigenVar )
          go( child, Set( eigenVar ) )
        case ETtSkolem( skTerm, _, child ) =>
          go( child, below ++ freeVariables( skTerm ) )
        case ETtDef( _, child ) =>
          go( child, below )
      }
    for ( et <- es ) go( et.term, Set.empty )
    out.toSet
  }

  implicit object closedUnderSubst extends ClosedUnderSub[ExpansionProof] {
    override def applySubstitution( subst: Substitution, expansionProof: ExpansionProof ): ExpansionProof =
      if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
        applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
      } else {
        val substWithRenaming = subst compose Substitution(
          rename(
            expansionProof.eigenVariables intersect subst.range,
            expansionProof.eigenVariables union subst.range ) )
        ExpansionProof( substWithRenaming( expansionProof.expansionSequent ) )
      }
  }

  implicit object closedUnderRepl extends ClosedUnderReplacement[ExpansionProof] {
    def replace( ep: ExpansionProof, p: PartialFunction[Expr, Expr] ): ExpansionProof =
      ExpansionProof( TermReplacement( ep.expansionSequent, p ) )

    def names( ep: ExpansionProof ): Set[VarOrConst] =
      containedNames( ep.expansionSequent )
  }

  implicit object checkable extends Checkable[ExpansionProof] {
    def check( ep: ExpansionProof )( implicit ctx: Context ): Unit =
      ep.expansionSequent.foreach( _.check()( ctx ) )
  }
}

object freeVariablesET {
  def apply( expansionProof: ExpansionProof ): Set[Var] =
    freeVariables( expansionProof.deep ) diff expansionProof.eigenVariables
}