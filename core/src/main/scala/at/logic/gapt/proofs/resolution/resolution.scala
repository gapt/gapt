package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.{ ContextRule, DagProof, HOLClause, HOLSequent, OccConnector, Sequent, SequentIndex, SequentProof, Suc }

import scala.collection.mutable

trait ResolutionProof extends SequentProof[HOLFormula, ResolutionProof] with DagProof[ResolutionProof] {
  val assertions: HOLClause = immediateSubProofs.map( _.assertions ).fold( Sequent() )( _ ++ _ ).distinct

  def introducedDefinitions: Map[HOLAtomConst, LambdaExpression] = Map()
  def definitions = {
    val builder = mutable.Map[HOLAtomConst, LambdaExpression]()
    for {
      p <- subProofs
      ( defConst, definition ) <- p.introducedDefinitions
    } if ( builder contains defConst )
      requireEq( builder( defConst ), definition )
    else
      builder( defConst ) = definition
    builder.toMap
  }

  override protected def stepString( subProofLabels: Map[Any, String] ) = {
    val assertionString =
      if ( assertions.isEmpty ) ""
      else s"   <-- ${assertions.map( identity, -_ ).elements.mkString( "," )} "
    s"$conclusion$assertionString   (${super[DagProof].stepString( subProofLabels )})"
  }

  def isProof = {
    definitions
    conclusion.isEmpty && assertions.isEmpty
  }

  private[resolution] def requireEq[T]( a: T, b: T ) =
    require( a == b, s"\n$a ==\n$b" )
}

abstract class LocalResolutionRule extends ResolutionProof with ContextRule[HOLFormula, ResolutionProof]

abstract class InitialClause extends LocalResolutionRule {
  override def auxIndices = Seq()
  override def immediateSubProofs = Seq()
}
case class Input( sequent: HOLSequent ) extends InitialClause {
  override def mainFormulaSequent = sequent
}
case class Taut( formula: HOLFormula ) extends InitialClause {
  override def mainFormulaSequent = formula +: Sequent() :+ formula
}
case class Refl( term: LambdaExpression ) extends InitialClause {
  override def mainFormulaSequent = Sequent() :+ ( term === term )
}

case class Factor( subProof: ResolutionProof, idx1: SequentIndex, idx2: SequentIndex ) extends LocalResolutionRule {
  require( idx1 sameSideAs idx2 )
  require( idx1 < idx2 )
  requireEq( subProof.conclusion( idx1 ), subProof.conclusion( idx2 ) )
  override def mainFormulaSequent =
    if ( idx1 isAnt ) subProof.conclusion( idx1 ) +: Sequent()
    else Sequent() :+ subProof.conclusion( idx1 )
  override def immediateSubProofs = Seq( subProof )
  override def auxIndices = Seq( Seq( idx1, idx2 ) )
}
object Factor {
  def apply( p: ResolutionProof ): ResolutionProof =
    apply( p, p.conclusion.distinct )
  def apply( p: ResolutionProof, newConclusion: HOLSequent ): ResolutionProof = {
    var p_ = p
    for ( ( a, i ) <- p.conclusion.diff( newConclusion ).zipWithIndex ) {
      val Seq( j1, j2, _* ) = p_.conclusion.zipWithIndex.elements.filter( _._2 sameSideAs i ).filter( _._1 == a ).map( _._2 )
      p_ = Factor( p_, j1, j2 )
    }
    p_
  }
  def withOccConn( p: ResolutionProof ): ( ResolutionProof, OccConnector[HOLFormula] ) = {
    var p_ = p
    var conn = OccConnector( p_.conclusion )
    for ( ( a, i ) <- p.conclusion.diff( p.conclusion.distinct ).zipWithIndex ) {
      val Seq( j1, j2, _* ) = p_.conclusion.zipWithIndex.elements.filter( _._2 sameSideAs i ).filter( _._1 == a ).map( _._2 )
      p_ = Factor( p_, j1, j2 )
      conn = p_.occConnectors.head * conn
    }
    p_ -> conn
  }
}
object MguFactor {
  def apply( p: ResolutionProof, i1: SequentIndex, i2: SequentIndex ): ResolutionProof = {
    val Some( mgu ) = syntacticMGU( p.conclusion( i1 ), p.conclusion( i2 ) )
    Factor( Subst( p, mgu ), i1, i2 )
  }
}

case class Subst( subProof: ResolutionProof, substitution: Substitution ) extends ResolutionProof {
  override def conclusion: Sequent[HOLFormula] = subProof.conclusion.map( substitution( _ ) ).map( BetaReduction.betaNormalize )
  override def mainIndices: Seq[SequentIndex] = subProof.conclusion.indices
  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( subProof.conclusion.indices )
  override def occConnectors: Seq[OccConnector[HOLFormula]] =
    Seq( OccConnector( conclusion, subProof.conclusion, subProof.conclusion.indicesSequent.map( Seq( _ ) ) ) )
  override def immediateSubProofs: Seq[ResolutionProof] = Seq( subProof )
}

case class Resolution( subProof1: ResolutionProof, idx1: SequentIndex,
                       subProof2: ResolutionProof, idx2: SequentIndex ) extends LocalResolutionRule {
  require( idx1 isSuc )
  require( idx2 isAnt )
  requireEq( subProof1.conclusion( idx1 ), subProof2.conclusion( idx2 ) )
  def resolvedLiteral = subProof1.conclusion( idx1 )

  def mainFormulaSequent = Sequent()
  def immediateSubProofs = Seq( subProof1, subProof2 )
  def auxIndices = Seq( Seq( idx1 ), Seq( idx2 ) )
}
object MguResolution {
  def apply( subProof1: ResolutionProof, idx1: SequentIndex,
             subProof2: ResolutionProof, idx2: SequentIndex ): ResolutionProof = {
    val renaming = Substitution( rename( freeVariables( subProof1.conclusion ), freeVariables( subProof2.conclusion ) ) )
    val Some( mgu ) = syntacticMGU( renaming( subProof1.conclusion( idx1 ) ), subProof2.conclusion( idx2 ) )
    Resolution( Subst( subProof1, mgu compose renaming ), idx1, Subst( subProof2, mgu ), idx2 )
  }
}

case class Paramod( subProof1: ResolutionProof, eqIdx: SequentIndex, leftToRight: Boolean,
                    subProof2: ResolutionProof, auxIdx: SequentIndex,
                    context: LambdaExpression ) extends LocalResolutionRule {
  require( eqIdx isSuc )
  val ( t, s ) = subProof1.conclusion( eqIdx ) match { case Eq( t_, s_ ) => if ( leftToRight ) ( t_, s_ ) else ( s_, t_ ) }

  def auxFormula = subProof2.conclusion( auxIdx )
  require(
    auxFormula == BetaReduction.betaNormalize( context( t ) ),
    s"$auxFormula == ${BetaReduction.betaNormalize( context( t ) )}"
  )
  val rewrittenAuxFormula = BetaReduction.betaNormalize( context( s ) ).asInstanceOf[HOLFormula]
  def mainFormulaSequent =
    if ( auxIdx isAnt ) rewrittenAuxFormula +: Sequent()
    else Sequent() :+ rewrittenAuxFormula

  def immediateSubProofs = Seq( subProof1, subProof2 )
  def auxIndices = Seq( Seq( eqIdx ), Seq( auxIdx ) )
}
object Paramod {
  def withMain( subProof1: ResolutionProof, eqIdx: SequentIndex,
                subProof2: ResolutionProof, auxIdx: SequentIndex,
                main: HOLFormula ): ResolutionProof = {
    val Eq( t, s ) = subProof1.conclusion( eqIdx )

    val ctxLTR = replacementContext( t.exptype, main,
      subProof2.conclusion( auxIdx ).find( t ).filter( main get _ contains s ) )
    val ctxRTL = replacementContext( t.exptype, main,
      subProof2.conclusion( auxIdx ).find( s ).filter( main get _ contains t ) )

    if ( BetaReduction.betaNormalize( ctxLTR( t ) ) == subProof2.conclusion( auxIdx )
      && BetaReduction.betaNormalize( ctxLTR( s ) ) == main ) {
      Paramod( subProof1, eqIdx, true, subProof2, auxIdx, ctxLTR )
    } else {
      Paramod( subProof1, eqIdx, false, subProof2, auxIdx, ctxRTL )
    }
  }
}

case class AvatarSplit(
    subProof:   ResolutionProof,
    components: Seq[AvatarComponent]
) extends ResolutionProof {
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
}
case class AvatarNonGroundComp( atom: HOLAtom, definition: HOLFormula, vars: Seq[Var] ) extends AvatarComponent {
  require( atom.isInstanceOf[HOLAtomConst] )
  private val AvatarNonGroundComp.DefinitionFormula( canonVars, canonicalClause ) = definition

  private val subst = Substitution( canonVars zip vars )
  require( vars.size == canonVars.size )
  require( subst isInjectiveRenaming )

  def disjunction = instantiate( definition, vars )

  def assertion = Sequent() :+ atom
  val clause = Substitution( canonVars zip vars )( canonicalClause )
  def inducedDefinitions = Map( atom.asInstanceOf[HOLAtomConst] -> definition )
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

abstract class PropositionalResolutionRule extends LocalResolutionRule {
  def subProof: ResolutionProof
  def idx: SequentIndex

  override def immediateSubProofs = Seq( subProof )
  override def auxIndices = Seq( Seq( idx ) )
}

case class DefIntro( subProof: ResolutionProof, idx: SequentIndex,
                     defAtom: HOLAtom, definition: LambdaExpression ) extends PropositionalResolutionRule {
  val Apps( defConst: HOLAtomConst, defArgs ) = defAtom
  requireEq( subProof.conclusion( idx ), BetaReduction.betaNormalize( definition( defArgs: _* ) ) )
  override def introducedDefinitions = Map( defConst -> definition )
  override def mainFormulaSequent =
    if ( idx isAnt ) defAtom +: Sequent()
    else Sequent() :+ defAtom
}

case class TopL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Top() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
}
case class BottomR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Bottom() = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent()
}
case class NegL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Neg( sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub
}
case class NegR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Neg( sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub +: Sequent()
}
case class AndL( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: sub2 +: Sequent()
}
case class OrR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1 :+ sub2
}
case class ImpR( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: Sequent() :+ sub2
}
case class AndR1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1
}
case class OrL1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub1 +: Sequent()
}
case class ImpL1( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub1
}
case class AndR2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isSuc )
  val And( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ sub2
}
case class OrL2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Or( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub2 +: Sequent()
}
case class ImpL2( subProof: ResolutionProof, idx: SequentIndex ) extends PropositionalResolutionRule {
  require( idx isAnt )
  val Imp( sub1, sub2 ) = subProof.conclusion( idx )
  def mainFormulaSequent = sub2 +: Sequent()
}

abstract class WeakQuantResolutionRule extends PropositionalResolutionRule {
  def variable: Var
  def bound: Var
  def sub: HOLFormula
  def instFormula = Substitution( bound -> variable )( sub )

  // FIXME: is eigenvariable condition a good idea?
  require( !freeVariables( subProof.conclusion ).contains( variable ) )
}
case class AllR( subProof: ResolutionProof, idx: SequentIndex, variable: Var ) extends WeakQuantResolutionRule {
  require( idx isSuc )
  val All( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ instFormula
}
object AllR {
  object Block {
    def apply( subProof: ResolutionProof, idx: SequentIndex, vars: Seq[Var] ): ResolutionProof = vars match {
      case v +: vs =>
        apply( AllR( subProof, idx, v ), subProof.conclusion.indices.last, vs )
      case Seq() => subProof
    }
    def apply( subProof: ResolutionProof, idx: SequentIndex ): ResolutionProof = {
      val All.Block( vs, _ ) = subProof.conclusion( idx )
      apply( subProof, idx, vs )
    }
  }
}
case class ExL( subProof: ResolutionProof, idx: SequentIndex, variable: Var ) extends WeakQuantResolutionRule {
  require( idx isAnt )
  val Ex( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = instFormula +: Sequent()
}

abstract class SkolemQuantResolutionRule extends PropositionalResolutionRule {
  def skolemTerm: LambdaExpression
  def skolemDef: LambdaExpression
  def bound: Var
  def sub: HOLFormula

  val Apps( skolemConst: Const, skolemArgs ) = skolemTerm
  requireEq( BetaReduction.betaNormalize( skolemDef( skolemArgs: _* ) ), subProof.conclusion( idx ) )

  def instFormula = Substitution( bound -> skolemTerm )( sub )
}
case class AllL( subProof: ResolutionProof, idx: SequentIndex, skolemTerm: LambdaExpression, skolemDef: LambdaExpression ) extends SkolemQuantResolutionRule {
  require( idx isAnt )
  val All( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = instFormula +: Sequent()
}
case class ExR( subProof: ResolutionProof, idx: SequentIndex, skolemTerm: LambdaExpression, skolemDef: LambdaExpression ) extends SkolemQuantResolutionRule {
  require( idx isSuc )
  val Ex( bound, sub ) = subProof.conclusion( idx )
  def mainFormulaSequent = Sequent() :+ instFormula
}

object Flip {
  def apply( subProof: ResolutionProof, equation: SequentIndex ): ResolutionProof = {
    val Eq( s, t ) = subProof.conclusion( equation )
    val x = rename( Var( "x", s.exptype ), freeVariables( subProof.conclusion ) )
    if ( equation isSuc ) {
      Paramod( subProof, equation, true,
        Refl( s ), Suc( 0 ), Abs( x, Eq( x, s ) ) )
    } else {
      Resolution(
        Paramod( Taut( Eq( t, s ) ), Suc( 0 ), false,
          Refl( s ), Suc( 0 ), Abs( x, Eq( s, x ) ) ), Suc( 0 ),
        subProof, equation
      )
    }
  }
}

