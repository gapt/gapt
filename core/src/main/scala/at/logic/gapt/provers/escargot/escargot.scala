package at.logic.gapt.provers.escargot

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TptpParser, resolutionToTptp, tptpProblemToResolution }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.{ ResolutionProver, groundFreeVariables }
import at.logic.gapt.provers.escargot.impl.{ EscargotState, StandardInferences }
import at.logic.gapt.utils.Logger
import ammonite.ops._

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

  def makeVerbose() = Logger.makeVerbose( classOf[EscargotState] )

  def main( args: Array[String] ): Unit = {
    Logger.useTptpComments()

    val tptpInputFile = args.toSeq match {
      case Seq() =>
        println( "Usage: escargot [-v] tptp-problem.p" )
        sys.exit( 1 )
      case Seq( "-v", file ) =>
        makeVerbose()
        file
      case Seq( file ) => file
    }

    val tptp = TptpParser.load( FilePath( tptpInputFile ) )
    getResolutionProof( structuralCNF.onProofs( tptpProblemToResolution( tptp ) ) ) match {
      case Some( proof ) =>
        println( "% SZS status Unsatisfiable" )
        println( "% SZS output start CNFRefutation" )
        print( resolutionToTptp( proof ) )
        println( "% SZS output end CNFRefutation" )
      case None =>
        println( "% SZS status Satisfiable" )
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

  def getAtomicLKProof( sequent: HOLClause ): Option[LKProof] =
    groundFreeVariables.wrap( sequent ) { sequent =>
      getResolutionProof( sequent.map( _.asInstanceOf[HOLAtom] ).
        map( Sequent() :+ _, _ +: Sequent() ).elements ) map { resolution =>
        UnitResolutionToLKProof( resolution )
      }
    }
}
