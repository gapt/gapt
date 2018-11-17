package gapt.cutintro

import gapt.expr._
import gapt.expr.fol.isFOLPrenexSigma1
import gapt.expr.hol.containsQuantifier
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.proofs.expansion._
import gapt.provers.Prover

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

  def toExpansionProof = {
    val nonCutPart: Sequent[ExpansionTree] = sehs.us.zipWithIndex map {
      case ( ( u, insts ), idx ) =>
        val Some( ( vs, f ) ) = if ( idx.isAnt ) All.Block.unapply( u ) else Ex.Block.unapply( u )
        ETWeakQuantifierBlock( u, vs.size,
          for ( inst <- insts ) yield inst -> formulaToExpansionTree( Substitution( vs zip inst )( f ), idx.polarity ) )
    }

    val cuts = ETCut {
      for ( ( ( eigenVar, cutImplInst ), formula ) <- sehs.ss zip formulas )
        yield (
        ETStrongQuantifierBlock( All.Block( eigenVar, formula ), eigenVar,
          formulaToExpansionTree( formula, Polarity.Positive ) ),
          ETWeakQuantifierBlock( All.Block( eigenVar, formula ), eigenVar.size,
            for ( inst <- cutImplInst ) yield inst ->
              formulaToExpansionTree( Substitution( eigenVar zip inst )( formula ), Polarity.Negative ) ) )
    }

    eliminateMerges( ExpansionProof( cuts +: nonCutPart ) )
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

  def getDeep: HOLSequent = toExpansionProof.deep

  override def toString = getDeep.toString
}
