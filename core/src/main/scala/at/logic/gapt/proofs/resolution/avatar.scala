package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs._

case class AvatarSplit(
    subProof:   ResolutionProof,
    components: Seq[AvatarComponent]
) extends ResolutionProof {
  for ( c <- components ) require( !c.introOnly )
  for ( ( c1, i1 ) <- components.zipWithIndex; ( c2, i2 ) <- components.zipWithIndex if i1 != i2 )
    require( freeVariables( c1.clause ) intersect freeVariables( c2.clause ) isEmpty )

  // FIXME: should we really handle duplicate components?
  require( subProof.conclusion isSubMultisetOf components.map( _.clause ).fold( Sequent() )( _ ++ _ ) )

  override def introducedDefinitions = components.view.flatMap( _.inducedDefinitions ).toMap

  override val assertions = ( subProof.assertions ++ components.map( _.assertion ).fold( Sequent() )( _ ++ _ ) ).distinct

  def mainIndices = Seq()
  def auxIndices = Seq( subProof.conclusion.indices )
  def conclusion = Sequent()
  def occConnectors = Seq( OccConnector( conclusion, subProof.conclusion, Sequent() ) )
  def immediateSubProofs = Seq( subProof )
}
case class AvatarComponentIntro( component: AvatarComponent ) extends InitialClause {
  override def introducedDefinitions = component.inducedDefinitions
  override val assertions = component.assertion.swapped
  def mainFormulaSequent = component.clause
}

trait AvatarComponent {
  def clause: HOLSequent
  def assertion: HOLClause
  def inducedDefinitions: Map[HOLAtomConst, LambdaExpression]
  def introOnly = false
}
abstract class AvatarGeneralNonGroundComp extends AvatarComponent {
  def atom: HOLAtom
  def definition: HOLFormula
  def vars: Seq[Var]

  require( atom.isInstanceOf[HOLAtomConst] )
  protected val AvatarNonGroundComp.DefinitionFormula( canonVars, canonicalClause ) = definition

  protected val subst = Substitution( canonVars zip vars )
  require( vars.size == canonVars.size )
  require( subst isInjectiveRenaming )

  def disjunction = instantiate( definition, vars )

  def inducedDefinitions = Map( atom.asInstanceOf[HOLAtomConst] -> definition )

  val componentClause = subst( canonicalClause )
}
case class AvatarNonGroundComp( atom: HOLAtom, definition: HOLFormula, vars: Seq[Var] ) extends AvatarGeneralNonGroundComp {
  def assertion = Sequent() :+ atom
  def clause = componentClause
}
case class AvatarNegNonGroundComp( atom: HOLAtom, definition: HOLFormula, vars: Seq[Var], idx: SequentIndex ) extends AvatarGeneralNonGroundComp {
  require( freeVariables( componentClause( idx ) ).isEmpty )
  def assertion = atom +: Sequent()
  val propAtom = componentClause( idx )
  def clause = if ( idx.isSuc ) propAtom +: Sequent() else Sequent() :+ propAtom
  override def introOnly = true
}
object AvatarNonGroundComp {
  def apply( atom: HOLAtom, definition: HOLFormula ): AvatarNonGroundComp = {
    val All.Block( vs, _ ) = definition
    AvatarNonGroundComp( atom, definition, vs )
  }

  object DefinitionFormula {
    def apply( clause: HOLSequent ): HOLFormula =
      apply( freeVariables( clause ).toSeq, clause )
    def apply( vars: Seq[Var], clause: HOLSequent ) = {
      require( vars.toSet subsetOf freeVariables( clause ) )
      All.Block( vars, clause.toDisjunction )
    }
    def unapply( f: HOLFormula ): Some[( Seq[Var], HOLSequent )] = f match {
      case All.Block( vars, litDisj ) =>
        val Or.nAry( lits ) = litDisj
        Some( ( vars, lits.map {
          case Neg( a ) => a +: Sequent()
          case a        => Sequent() :+ a
        }.fold( Sequent() )( _ ++ _ ) ) )
    }
  }
}
case class AvatarGroundComp( atom: HOLAtom, polarity: Boolean ) extends AvatarComponent {
  require( freeVariables( atom ).isEmpty )
  def assertion = if ( polarity ) Sequent() :+ atom else atom +: Sequent()
  def clause = assertion
  def inducedDefinitions = Map()
}

case class AvatarAbsurd( subProof: ResolutionProof ) extends LocalResolutionRule {
  override val assertions = Sequent()
  def mainFormulaSequent = subProof.assertions
  def auxIndices = Seq( Seq() )
  def immediateSubProofs = Seq( subProof )
}

