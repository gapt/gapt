package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsQuantifierOnLogicalLevel, containsStrongQuantifier, instantiate }
import at.logic.gapt.grammars.{ RecursionScheme, Rule }
import at.logic.gapt.proofs.expansion.linearizeStrictPartialOrder
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.{ LKProof, TheoryAxiom, WeakeningMacroRule, cleanStructuralRules }
import at.logic.gapt.proofs.{ Context, HOLSequent, Sequent }
import at.logic.gapt.provers.{ OneShotProver, Prover }

trait SchematicProofWithInduction {
  def endSequent: HOLSequent
  def solutionCondition: HOLFormula
  def lkProof( solution: Seq[LambdaExpression], prover: Prover ): LKProof
}

case class ProofByRecursionScheme(
    endSequent: HOLSequent,
    recSchem:   RecursionScheme,
    context:    Context
) extends SchematicProofWithInduction {
  private implicit def ctx = context

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
  val Right( dependencyOrder ) = linearizeStrictPartialOrder( recSchem.nonTerminals, dependencyRelation )

  val hoVarMapping = for {
    nt @ Const( v, t ) <- dependencyOrder.reverse
    if nt != recSchem.axiom
  } yield nt -> Var( s"X_$v", t )
  val hoVars = hoVarMapping.map( _._2 )
  val hoVarMap = hoVarMapping.toMap

  val solutionConditions = {
    val conds = Seq.newBuilder[HOLSequent]
    lkProof( hoVars, new OneShotProver {
      def getLKProof( seq: HOLSequent ) = {
        conds += seq
        Some( WeakeningMacroRule( TheoryAxiom( Sequent() ), seq ) )
      }
    } )
    conds.result()
  }

  val solutionCondition = Ex.Block(
    hoVars,
    And( solutionConditions.map( cond =>
      All.Block( freeVariables( cond ).toSeq.diff( hoVars ), cond.toImplication ) ) )
  )

  //  val solutionCondition @ Ex.Block( hoVars, _ ) = qbupForRecSchem( recSchem, conj )

  def lemma( solution: Seq[LambdaExpression], nonTerminal: Const ) = {
    val FunctionType( _, argTypes ) = nonTerminal.exptype
    val args = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x_$i", t )
    All.Block(
      args,
      BetaReduction.betaNormalize( solution( hoVars.indexOf( hoVarMap( nonTerminal ) ) )( args ) )
    ).asInstanceOf[HOLFormula]
  }

  def mkInsts( state0: ProofState, solution: Seq[LambdaExpression], lhsPattern: LambdaExpression ) = {
    var state = state0
    val instanceTerms = for {
      Rule( lhs, rhs ) <- recSchem.rules
      subst <- syntacticMatching( lhs, lhsPattern )
    } yield subst( rhs )
    instanceTerms.foreach {
      case Apps( nt: Const, args ) if recSchem.nonTerminals.contains( nt ) =>
        state += haveInstance( instantiate( lemma( solution, nt ), args ), Polarity.InAntecedent )
      case Neg( form )      => state += haveInstance( form, Polarity.InAntecedent ).orElse( haveInstance( -form, Polarity.InSuccedent ) )
      case form: HOLFormula => state += haveInstance( form, Polarity.InAntecedent )
    }
    for {
      ( label, form ) <- state.currentSubGoalOption.get.labelledSequent
      if containsQuantifierOnLogicalLevel( form )
    } state += forget( label )
    state
  }

  def mkLemma( solution: Seq[LambdaExpression], nonTerminal: Const, prover: Prover ) = {
    val lem @ All.Block( vs, matrix ) = lemma( solution, nonTerminal )

    val prevLems = for ( prevNT <- dependencyOrder.takeWhile( _ != nonTerminal ) )
      yield s"lem_${prevNT.name}" -> lemma( solution, prevNT )

    var state = ProofState( prevLems ++: theory :+ ( "goal" -> lem ) )

    val indArgs = for {
      Rule( Apps( `nonTerminal`, args ), _ ) <- recSchem.rules
      ( a, i ) <- args.zipWithIndex
      if !a.isInstanceOf[Var]
    } yield i

    state += vs.indices.map( i =>
      if ( indArgs( i ) ) allR( "goal" ).flatMap( induction( _, "goal" ) ).asTactic
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

  def lkProof( solution: Seq[LambdaExpression], prover: Prover ): LKProof = {
    var state = ProofState( theory :+ ( "goal" -> conj ) )
    for ( nt <- dependencyOrder if nt != recSchem.axiom ) {
      val lem = lemma( solution, nt )
      state += cut( s"lem_${nt.name}", lem )
      state += insert( mkLemma( solution, nt, prover ) )
    }

    for ( v <- paramVars ) state += allR( v )
    state = mkInsts( state, solution, recSchem.axiom( paramVars ) )
    val proof = prover.getLKProof( state.currentSubGoalOption.get.conclusion ).
      getOrElse( throw new Exception( s"Unprovable: ${state.currentSubGoalOption.get}" ) )
    state += insert( proof )

    cleanStructuralRules( state.result )
  }

}