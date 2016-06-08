package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs._

object AvatarSplit {
  def apply( subProof: ResolutionProof, components: Seq[AvatarComponent] ): ResolutionProof =
    components.foldLeft( subProof )( AvatarComponentElim( _, _ ) )
}
case class AvatarComponentElim( subProof: ResolutionProof, indices: Set[SequentIndex], component: AvatarComponent ) extends LocalResolutionRule {
  require( !component.introOnly )
  require( indices subsetOf subProof.conclusion.indices.toSet )

  val thisComponent = subProof.conclusion.zipWithIndex.filter( indices contains _._2 ).map( _._1 )
  val rest = subProof.conclusion.zipWithIndex.filterNot( indices contains _._2 ).map( _._1 )
  require( freeVariables( thisComponent ) intersect freeVariables( rest ) isEmpty )
  require( component.clause isSubMultisetOf thisComponent )

  override def auxIndices = Seq( indices.toSeq )
  override def mainFormulaSequent = Sequent()
  override val assertions = subProof.assertions ++ component.assertion distinct
  override def immediateSubProofs = Seq( subProof )
  override def introducedDefinitions = component.inducedDefinitions
}
object AvatarComponentElim {
  def apply( subProof: ResolutionProof, component: AvatarComponent ): AvatarComponentElim = {
    def getIndices( toFind: HOLSequent ): Set[SequentIndex] =
      if ( toFind.isEmpty ) {
        Set()
      } else {
        val i = toFind.indices.head
        val indices = getIndices( toFind.delete( i ) )
        subProof.conclusion.indices.
          find( j => !indices.contains( j ) && i.sameSideAs( j ) && toFind( i ) == subProof.conclusion( j ) ).
          fold( indices )( indices + _ )
      }
    require( subProof.conclusion.delete( getIndices( component.clause ).toSeq: _* ) == subProof.conclusion.diff( component.clause ) )
    AvatarComponentElim( subProof, getIndices( component.clause ), component )
  }
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

