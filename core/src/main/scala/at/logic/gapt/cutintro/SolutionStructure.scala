package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion.{ ETImp, ETStrongQuantifierBlock, ETWeakQuantifierBlock, ExpansionProofWithCut, eliminateMerges, formulaToExpansionTree }
import at.logic.gapt.provers.Prover

case class SolutionStructure( sehs: SchematicExtendedHerbrandSequent, formulas: Seq[FOLFormula] ) {
  require( formulas.size == sehs.ss.size )
  require( isFOLPrenexSigma1( endSequent ) )

  for ( ( f, i ) <- formulas.zipWithIndex ) {
    require( !containsQuantifier( f ) )
    val allowedVars = sehs.ss.drop( i ).flatMap( _._1 )
    require( freeVariables( f ) subsetOf allowedVars.toSet )
  }

  def endSequent = sehs.us map { _._1 }

  def cutFormulas = for ( ( evs, f ) <- sehs.eigenVariables zip formulas ) yield All.Block( evs, f )

  /** Instances of the quantified and propositional formulas in the end-sequent. */
  def endSequentInstances = sehs.endSequentInstances

  def toExpansionProofWithCut = {
    val nonCutPart = sehs.us.zipWithIndex map {
      case ( ( u, insts ), idx ) =>
        val Some( ( vs, f ) ) = if ( idx.isAnt ) All.Block.unapply( u ) else Ex.Block.unapply( u )
        ETWeakQuantifierBlock( u, vs.size,
          for ( inst <- insts ) yield inst -> formulaToExpansionTree( Substitution( vs zip inst )( f ), idx.polarity ) )
    }

    val cuts = for ( ( ( eigenVar, cutImplInst ), formula ) <- sehs.ss zip formulas )
      yield ETImp(
      ETStrongQuantifierBlock( All.Block( eigenVar, formula ), eigenVar, formulaToExpansionTree( formula, Polarity.Positive ) ),
      ETWeakQuantifierBlock( All.Block( eigenVar, formula ), eigenVar.size,
        for ( inst <- cutImplInst ) yield inst -> formulaToExpansionTree( Substitution( eigenVar zip inst )( formula ), Polarity.Negative ) ) )

    eliminateMerges( ExpansionProofWithCut( cuts, nonCutPart ) )
  }

  def instantiatedSolutionCondition( i: Int ) = {
    val esInsts = sehs.esInstancesInScope( i + 1 )
    val lowerCuts = formulas.drop( i + 1 )
    val cutInsts = if ( i == -1 ) Seq() else sehs.substitutions( i ).map( _( formulas( i ) ) )
    cutInsts ++: esInsts :++ lowerCuts
  }

  def instantiatedSolutionConditions =
    for ( i <- -1 until formulas.size ) yield instantiatedSolutionCondition( i )

  def isValid( prover: Prover ): Boolean =
    instantiatedSolutionConditions forall prover.isValid

  def getDeep: HOLSequent = toExpansionProofWithCut.deep

  override def toString = getDeep.toString
}
