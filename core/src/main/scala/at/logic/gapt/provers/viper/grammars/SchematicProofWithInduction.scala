package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsQuantifierOnLogicalLevel, containsStrongQuantifier, instantiate, universalClosure }
import at.logic.gapt.grammars.{ RecursionScheme, Rule }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, TheoryAxiom, WeakeningMacroRule, cleanStructuralRules }
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, Sequent }
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.utils.{ Maybe, linearizeStrictPartialOrder }

trait SchematicProofWithInduction {
  def endSequent: HOLSequent
  def solutionCondition: Formula
  def lkProof( solution: Seq[Expr], prover: Prover, equationalTheory: Seq[Formula] ): LKProof

  def paramVars: Seq[Var]
  def generatedLanguage( inst: Seq[Expr] ): Set[Formula]
}

case class ProofByRecursionScheme(
    endSequent: HOLSequent,
    recSchem:   RecursionScheme,
    context:    Context ) extends SchematicProofWithInduction {
  private implicit def ctx = context

  override def toString = recSchem.toString

  val theory = for {
    ( f, i ) <- endSequent.zipWithIndex
    if !containsStrongQuantifier( f, i.polarity )
  } yield s"th_$i".replace( ")", "" ).replace( "(", "" ) -> f
  val Sequent( _, Seq( conj @ All.Block( paramVars, _ ) ) ) = endSequent

  val dependencyRelation = for {
    Rule( Apps( nt1: Const, _ ), Apps( nt2: Const, _ ) ) <- recSchem.rules
    if nt1 != nt2
    if recSchem.nonTerminals.contains( nt1 )
    if recSchem.nonTerminals.contains( nt2 )
  } yield nt2 -> nt1
  val Right( dependencyOrder ) = linearizeStrictPartialOrder(
    recSchem.nonTerminals,
    dependencyRelation ++ recSchem.nonTerminals.filter( _ != recSchem.startSymbol ).map( _ -> recSchem.startSymbol ) )

  val hoVarMapping = for {
    nt @ Const( v, t ) <- dependencyOrder.reverse
    if nt != recSchem.startSymbol
  } yield nt -> Var( s"X_$v", t )
  val hoVars = hoVarMapping.map( _._2 )
  val hoVarMap = hoVarMapping.toMap

  lazy val solutionConditions = {
    val conds = Seq.newBuilder[HOLSequent]
    lkProof( hoVars, new OneShotProver {
      def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ) = {
        conds += seq
        Some( WeakeningMacroRule( TheoryAxiom( Sequent() ), seq ) )
      }
    }, Seq() )
    conds.result()
  }

  lazy val solutionCondition = Ex.Block(
    hoVars,
    And( solutionConditions.map( cond =>
      All.Block( freeVariables( cond ).toSeq.diff( hoVars ), cond.toImplication ) ) ) )

  //  val solutionCondition @ Ex.Block( hoVars, _ ) = qbupForRecSchem( recSchem, conj )

  def lemma( solution: Seq[Expr], nonTerminal: Const ) = {
    val FunctionType( _, argTypes ) = nonTerminal.ty
    val args = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x_$i", t )
    All.Block(
      args,
      BetaReduction.betaNormalize( solution( hoVars.indexOf( hoVarMap( nonTerminal ) ) )( args ) ) ).asInstanceOf[Formula]
  }

  def mkInsts( state0: ProofState, solution: Seq[Expr], lhsPattern: Expr ) = {
    var state = state0
    val instanceTerms = for {
      Rule( lhs, rhs ) <- recSchem.rules
      subst <- syntacticMatching( lhs, lhsPattern )
    } yield subst( rhs )
    instanceTerms.foreach {
      case Apps( nt: Const, args ) if recSchem.nonTerminals.contains( nt ) =>
        state += haveInstance( instantiate( lemma( solution, nt ), args ), Polarity.InAntecedent )
      case Neg( form )   => state += haveInstance( form, Polarity.InSuccedent ).orElse( haveInstance( -form, Polarity.InAntecedent ) )
      case form: Formula => state += haveInstance( form, Polarity.InAntecedent )
    }
    for {
      ( label, form ) <- state.currentSubGoalOption.get.labelledSequent
      if containsQuantifierOnLogicalLevel( form ) && !label.startsWith( "eq_" )
    } state += forget( label )
    state
  }

  def mkLemma( state0: ProofState, solution: Seq[Expr], nonTerminal: Const, prover: Prover ) = {
    val lem @ All.Block( vs, matrix ) = lemma( solution, nonTerminal )

    val prevLems = for ( prevNT <- dependencyOrder.takeWhile( _ != nonTerminal ) )
      yield s"lem_${prevNT.name}" -> lemma( solution, prevNT )

    var state = ProofState( state0.currentSubGoalOption.get )
    state += forget( "goal" )
    state += renameLabel( s"lem_${nonTerminal.name}" ).to( "goal" )

    val indArgs = for {
      Rule( Apps( `nonTerminal`, args ), _ ) <- recSchem.rules
      ( a, i ) <- args.zipWithIndex
      if !a.isInstanceOf[Var]
    } yield i

    state += vs.indices.map( i =>
      if ( indArgs( i ) ) allR( "goal" ).flatMap( induction( _, "goal" ) ).onCurrentSubGoal
      else allR( "goal" ) ).foldRight( TacticalMonad.pure( () ) )( _ onAll _ )

    while ( state.currentSubGoalOption.nonEmpty ) {
      val Some( subst ) = syntacticMatching( matrix, state.currentSubGoalOption.get( "goal" ) )
      val lhsPattern = nonTerminal( subst( vs ) )
      state = mkInsts( state, solution, lhsPattern )
      val proof = prover.getLKProof( state.currentSubGoalOption.get.conclusion ).
        getOrElse( throw new Exception( s"$nonTerminal is unprovable: ${state.currentSubGoalOption.get}" ) )
      state += insert( proof )
    }

    state.result
  }

  def lkProof( solution: Seq[Expr], prover: Prover, equationalTheory: Seq[Formula] ): LKProof = {
    var state = ProofState( theory :+ ( "goal" -> conj ) )

    for ( ( eq, i ) <- equationalTheory.zipWithIndex ) {
      val lem = universalClosure( eq )
      state += cut( s"eq_$i", lem )
      state += forget( "goal" )
      state += decompose
      val proof = prover.getLKProof( state.currentSubGoalOption.get.conclusion ).
        getOrElse( throw new Exception( s"Theory equation $eq is unprovable:\n${state.currentSubGoalOption.get}" ) )
      state += insert( proof )
    }

    for ( nt <- dependencyOrder if nt != recSchem.startSymbol ) {
      val lem = lemma( solution, nt )
      state += cut( s"lem_${nt.name}", lem )
      state += insert( mkLemma( state, solution, nt, prover ) )
    }

    for ( v <- paramVars ) state += allR( v )
    state = mkInsts( state, solution, recSchem.startSymbol( paramVars ) )
    val proof = prover.getLKProof( state.currentSubGoalOption.get.conclusion ).
      getOrElse( throw new Exception( s"Unprovable: ${state.currentSubGoalOption.get}" ) )
    state += insert( proof )

    cleanStructuralRules( state.result )
  }

  def generatedLanguage( inst: Seq[Expr] ) =
    recSchem.parametricLanguage( inst: _* ).map( _.asInstanceOf[Formula] )
}