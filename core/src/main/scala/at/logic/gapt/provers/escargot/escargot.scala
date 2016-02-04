package at.logic.gapt.provers.escargot

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TptpParser, resolutionToTptp, tptpProblemToResolution }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.impl.{ EscargotState, StandardInferences }
import at.logic.gapt.utils.logging.Logger

object Escargot extends Escargot( splitting = true, equality = true, propositional = false ) {
  def lpoHeuristic( cnf: Traversable[HOLSequent] ): LPO = {
    val consts = constants( cnf flatMap { _.elements } )

    val boolOnTermLevel = consts exists { case Const( _, FunctionType( _, from ) ) => from contains To }
    val types = consts flatMap { c => baseTypes( c.exptype ) }

    val atoms = for ( c <- consts; FunctionType( to, _ ) = c.exptype if to == To ) yield c
    val eqs = atoms collect { case c @ EqC( _ ) => c }
    val functions = for ( c <- consts; FunctionType( to, _ ) = c.exptype if to != To ) yield c

    val precedence = functions.toSeq.sortBy { arity( _ ) } ++ eqs ++ ( atoms diff eqs ).toSeq.sortBy { arity( _ ) }

    LPO( precedence, if ( boolOnTermLevel ) Set() else ( types - To ) map { ( _, To ) } )
  }

  def setupDefaults(
    state:     EscargotState,
    splitting: Boolean, equality: Boolean, propositional: Boolean
  ) = {
    val standardInferences = new StandardInferences( state, propositional )
    import standardInferences._

    // Preprocessing rules
    state.preprocessingRules :+= DuplicateDeletion
    if ( equality ) {
      state.preprocessingRules :+= ForwardUnitRewriting
      state.preprocessingRules :+= OrderEquations
      state.preprocessingRules :+= EqualityResolution
      state.preprocessingRules :+= ReflexivityDeletion
    }
    state.preprocessingRules :+= TautologyDeletion
    state.preprocessingRules :+= ClauseFactoring
    state.preprocessingRules :+= DuplicateDeletion
    state.preprocessingRules :+= SubsumptionInterreduction
    state.preprocessingRules :+= ForwardSubsumption

    // Inference rules
    state.inferences :+= ForwardSubsumption
    if ( equality ) state.inferences :+= ReflModEqDeletion
    state.inferences :+= BackwardSubsumption
    if ( equality ) {
      state.inferences :+= ForwardUnitRewriting
      state.inferences :+= BackwardUnitRewriting
    }
    if ( splitting ) state.inferences :+= AvatarSplitting
    state.inferences :+= OrderedResolution
    state.inferences :+= Factoring
    if ( equality ) {
      state.inferences :+= Superposition
      state.inferences :+= UnifyingEqualityResolution
    }
  }

  def main( args: Array[String] ): Unit =
    args.toSeq match {
      case Seq( tptpInputFile ) =>
        org.apache.log4j.Logger.getLogger( classOf[EscargotState] ).setLevel( org.apache.log4j.Level.DEBUG )

        val tptp = TptpParser.loadFile( tptpInputFile )
        getResolutionProof( structuralCNF.onProofs( tptpProblemToResolution( tptp ) ) ) match {
          case Some( proof ) =>
            println( "SZS status Unsatisfiable" )
            println( resolutionToTptp( proof ).mkString )
          case None =>
            println( "SZS status Satisfiable" )
        }
    }
}
object NonSplittingEscargot extends Escargot( splitting = false, equality = true, propositional = false )

class Escargot( splitting: Boolean, equality: Boolean, propositional: Boolean ) extends ResolutionProver {
  override def getResolutionProof( cnf: Traversable[HOLClause] ): Option[ResolutionProof] = {
    val hasEquality = equality && cnf.flatMap( _.elements ).exists { case Eq( _, _ ) => true; case _ => false }
    val isPropositional = propositional || cnf.flatMap { freeVariables( _ ) }.isEmpty

    val state = new EscargotState
    Escargot.setupDefaults( state, splitting, hasEquality, isPropositional )
    state.nameGen = rename.awayFrom( cnf.view.flatMap( constants( _ ) ).toSet )
    state.termOrdering = Escargot.lpoHeuristic( cnf )
    state.newlyDerived ++= cnf.map { state.InputCls }
    state.loop()
  }
}
