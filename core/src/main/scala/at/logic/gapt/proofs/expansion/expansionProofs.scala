package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemFunctions }
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
    }
  )

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

  override def toString = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) =
    expansionSequent.map( _.toSigRelativeString ).toString
}

case class ExpansionProofWithCut( expansionWithCutAxiom: ExpansionProof ) {
  import ExpansionProofWithCut._
  def expansionSequent = expansionWithCutAxiom.expansionSequent filter { _.shallow != cutAxiom }
  def eigenVariables = expansionWithCutAxiom.eigenVariables
  def deep = expansionWithCutAxiom.deep
  def shallow = expansionSequent map { _.shallow }
  def subProofs = expansionWithCutAxiom.subProofs
  def skolemFunctions = expansionWithCutAxiom.skolemFunctions

  val cuts = for {
    cutAxiomExpansion <- expansionWithCutAxiom.expansionSequent.antecedent
    if cutAxiomExpansion.shallow == cutAxiom
    cut <- cutAxiomExpansion( HOLPosition( 1 ) )
    cut1 <- cut( HOLPosition( 1 ) )
    cut2 <- cut( HOLPosition( 2 ) )
  } yield ETImp( cut1, cut2 )

  def toExpansionProof = {
    require( cuts.isEmpty )
    ExpansionProof( expansionSequent )
  }

  override def toString = expansionWithCutAxiom.toString
}
object ExpansionProofWithCut {
  val cutAxiom = hof"∀X (X ⊃ X)"
  def apply( expansionSequentWithCutAxiom: ExpansionSequent ): ExpansionProofWithCut =
    ExpansionProofWithCut( ExpansionProof( expansionSequentWithCutAxiom ) )
  def apply( cuts: Seq[ETImp], expansionSequent: Sequent[ExpansionTree] ): ExpansionProofWithCut =
    apply( mkCutAxiom( cuts ) +: expansionSequent )
  def mkCutAxiom( cuts: Seq[ETImp] ): ExpansionTree =
    ETWeakQuantifier.withMerge(
      ExpansionProofWithCut.cutAxiom,
      for ( cut @ ETImp( cut1, cut2 ) <- cuts ) yield cut1.shallow -> cut
    )
}

object freeVariablesET {
  def apply( expansionProof: ExpansionProof ): Set[Var] =
    freeVariables( expansionProof.deep ) diff expansionProof.eigenVariables
  def apply( expansionProofWithCut: ExpansionProofWithCut ): Set[Var] =
    apply( expansionProofWithCut.expansionWithCutAxiom )
}
private[expansion] object expansionProofSubstitution extends ClosedUnderSub[ExpansionProof] {
  override def applySubstitution( subst: Substitution, expansionProof: ExpansionProof ): ExpansionProof =
    if ( subst.domain intersect expansionProof.eigenVariables nonEmpty ) {
      applySubstitution( Substitution( subst.map -- expansionProof.eigenVariables ), expansionProof )
    } else {
      val substWithRenaming = subst compose Substitution(
        rename( expansionProof.eigenVariables intersect subst.range, expansionProof.eigenVariables union subst.range )
      )
      ExpansionProof( substWithRenaming( expansionProof.expansionSequent ) )
    }
}
private[expansion] object expansionProofWithCutSubstitution extends ClosedUnderSub[ExpansionProofWithCut] {
  override def applySubstitution( subst: Substitution, expansionProofWithCut: ExpansionProofWithCut ): ExpansionProofWithCut =
    ExpansionProofWithCut( subst( expansionProofWithCut.expansionWithCutAxiom ) )
}

