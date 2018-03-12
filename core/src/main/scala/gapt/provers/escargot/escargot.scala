package gapt.provers.escargot

import gapt.expr._
import gapt.formats.tptp.{ TptpParser, resolutionToTptp, tptpProblemToResolution }
import gapt.proofs._
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution._
import gapt.provers.{ ResolutionProver, groundFreeVariables }
import gapt.provers.escargot.impl.{ EscargotLogger, EscargotState, StandardInferences }
import gapt.utils.{ LogHandler, Maybe }
import ammonite.ops._

object Escargot extends Escargot( splitting = true, equality = true, propositional = false ) {
  def lpoHeuristic( cnf: Traversable[HOLSequent], extraConsts: Iterable[Const] ): LPO = {
    val consts = constants( cnf flatMap { _.elements } ) ++ extraConsts

    val boolOnTermLevel = consts exists { case Const( _, FunctionType( _, from ), _ ) => from contains To }
    val types = consts flatMap { c => baseTypes( c.ty ) }

    val atoms = for ( c <- consts; FunctionType( to, _ ) = c.ty if to == To ) yield c
    val eqs = atoms collect { case c @ EqC( _ ) => c }
    val functions = for ( c <- consts; FunctionType( to, _ ) = c.ty if to != To ) yield c

    val precedence = functions.toSeq.sortBy { arity( _ ) } ++ eqs ++ ( atoms diff eqs ).toSeq.sortBy { arity( _ ) }

    LPO( precedence, if ( boolOnTermLevel ) Set() else ( types - To ) map { ( _, To ) } )
  }

  def setupDefaults(
    state:     EscargotState,
    splitting: Boolean, equality: Boolean, propositional: Boolean ) = {
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

  def main( args: Array[String] ): Unit = {
    LogHandler.current.value = LogHandler.tstp

    val tptpInputFile = args.toSeq match {
      case Seq() =>
        println( "Usage: escargot [-v] tptp-problem.p" )
        sys.exit( 1 )
      case Seq( "-v", file ) =>
        LogHandler.verbosity.value = LogHandler.verbosity.value.increase( Seq( EscargotLogger ), 2 )
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
object QfUfEscargot extends Escargot( splitting = true, propositional = true, equality = true )

class Escargot( splitting: Boolean, equality: Boolean, propositional: Boolean ) extends ResolutionProver {
  override def getResolutionProof( cnf: Traversable[HOLClause] )( implicit ctx0: Maybe[MutableContext] ): Option[ResolutionProof] = {
    implicit val ctx: MutableContext = ctx0.getOrElse( MutableContext.guess( cnf ) )
    val hasEquality = equality && cnf.flatMap( _.elements ).exists { case Eq( _, _ ) => true; case _ => false }
    val isPropositional = propositional || cnf.flatMap { freeVariables( _ ) }.isEmpty

    val state = new EscargotState( ctx )
    Escargot.setupDefaults( state, splitting, hasEquality, isPropositional )
    state.nameGen = rename.awayFrom( ctx.constants.toSet ++ cnf.view.flatMap( constants( _ ) ) )
    state.termOrdering = Escargot.lpoHeuristic( cnf, ctx.constants )
    state.newlyDerived ++= cnf.map { state.InputCls }
    state.loop()
  }

  def getAtomicLKProof( sequent: HOLClause ): Option[LKProof] =
    groundFreeVariables.wrap( sequent ) { sequent =>
      getResolutionProof( sequent.map( _.asInstanceOf[Atom] ).
        map( Sequent() :+ _, _ +: Sequent() ).elements ) map { resolution =>
        UnitResolutionToLKProof( resolution )
      }
    }
}
