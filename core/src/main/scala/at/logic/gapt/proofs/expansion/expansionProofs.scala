package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.utils.linearizeStrictPartialOrder

import scala.collection.mutable

case class ExpansionProof( expansionSequent: Sequent[ExpansionTree] ) {
  for ( ( tree, index ) <- expansionSequent.zipWithIndex )
    require( tree.polarity == index.polarity, s"Wrong polarity, ${index.polarity} expected:\n$tree" )

  {
    val evs = mutable.Set[Var]()
    val fvs = freeVariables( shallow )
    for {
      tree <- expansionSequent
      ETStrongQuantifier( _, ev, _ ) <- tree.treeLike.postOrder
    } {
      require( !evs.contains( ev ), s"duplicate eigenvariable $ev" )
      require( !fvs.contains( ev ), s"eigenvariable $ev is free in shallow sequent" )
      evs += ev
    }
  }

  def shallow = expansionSequent.shallow
  def deep = expansionSequent.deep

  val subProofs = expansionSequent.elements flatMap { _.subProofs } toSet
  val eigenVariables = for ( ETStrongQuantifier( _, ev, _ ) <- subProofs ) yield ev

  val skolemFunctions = SkolemFunctions(
    subProofs collect {
      case sk: ETSkolemQuantifier => sk.skolemConst -> sk.skolemDef
    } )

  /**
   * Contains the pair (x, y) iff x occurs as a selected term in any sort of quantifier node
   * below the strong quantifier node introducing y.
   */
  val dependencyRelation = for {
    ETQuantifier( _, instances ) <- subProofs
    ( term, child ) <- instances
    ETStrongQuantifier( _, ev, _ ) <- child.subProofs
    evInTerm <- eigenVariables intersect freeVariables( term )
  } yield evInTerm -> ev
  val Right( linearizedDependencyRelation ) = linearizeStrictPartialOrder( eigenVariables, dependencyRelation )

  def cuts: Vector[ETImp] = expansionSequent.antecedent.flatMap { case ETCut( cuts ) => cuts case _ => Seq() }
  def inductions( implicit ctx: Context ): Vector[ETInduction.Induction] = expansionSequent.antecedent.flatMap { case ETInduction( inductions ) => inductions case _ => Seq() }
  def nonCutPart: ExpansionSequent = expansionSequent.filterNot( ETCut.isCutExpansion )
  def nonTheoryPart( implicit ctx: Context ): ExpansionSequent =
    expansionSequent.filterNot( et => ETCut.isCutExpansion( et ) || ETInduction.isInductionAxiomExpansion( et ) )

  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    expansionSequent.map( _.toSigRelativeString ).toString
}

object freeVariablesET {
  def apply( expansionProof: ExpansionProof ): Set[Var] =
    freeVariables( expansionProof.deep ) diff expansionProof.eigenVariables
}
private[expansion] object expansionProofSubstitution extends ClosedUnderSub[ExpansionProof] {
  override def applySubstitution( subst: Substitution, expansionProof: ExpansionProof ): ExpansionProof =
    if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
      applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
    } else {
      val substWithRenaming = subst compose Substitution(
        rename( expansionProof.eigenVariables intersect subst.range, expansionProof.eigenVariables union subst.range ) )
      ExpansionProof( substWithRenaming( expansionProof.expansionSequent ) )
    }
}
