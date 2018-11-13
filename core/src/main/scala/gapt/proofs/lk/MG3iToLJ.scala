package gapt.proofs.lk

import gapt.expr._

object MG3iToLJ {
  def apply( proof: LKProof ): LKProof = {
    val Seq( f ) = proof.conclusion.succedent
    val q = apply( proof, f, Map( f -> LogicalAxiom( f ) ) )
    require( q.conclusion.isSubsetOf( proof.conclusion ) )
    q
  }

  def apply( proof: LKProof, goal: Formula, projections: Map[Formula, LKProof] ): LKProof = {
    for ( ( f, pr ) <- projections ) {
      require( pr.conclusion.succedent == Seq( goal ) )
      require( pr.conclusion.antecedent.contains( f ) )
    }
    val result = proof match {
      case LogicalAxiom( atom )            => projections( atom )
      case proof @ ReflexivityAxiom( _ )   => CutRule( proof, projections( proof.mainFormula ), proof.mainFormula )
      case ContractionLeftRule( p, _, _ )  => apply( p, goal, projections )
      case ContractionRightRule( p, _, _ ) => apply( p, goal, projections )
      case WeakeningRightRule( p, _ )      => apply( p, goal, projections )
      case WeakeningLeftRule( p, f )       => WeakeningLeftRule( apply( p, goal, projections ), f )
      case proof @ CutRule( p1, _, p2, _ ) =>
        val q2 = apply( p2, goal, projections )
        if ( !q2.conclusion.antecedent.contains( proof.cutFormula ) ) q2 else {
          val leftGoal = goal | proof.cutFormula
          val q1 = apply( p1, leftGoal, Map() ++
            projections.mapValues( pr => CutRule( pr, OrRightMacroRule( LogicalAxiom( goal ), goal, proof.cutFormula ), goal ) ) +
            ( proof.cutFormula -> OrRightMacroRule( LogicalAxiom( proof.cutFormula ), goal, proof.cutFormula ) ) )
          ContractionMacroRule( CutRule( q1, OrLeftRule( LogicalAxiom( goal ), q2, leftGoal ), leftGoal ) )
        }
      case BottomAxiom => WeakeningRightRule( BottomAxiom, goal )
      case TopAxiom    => CutRule( TopAxiom, projections( Top() ), Top() )
      case proof @ EqualityLeftRule( p, _, _, cx ) =>
        ContractionMacroRule( EqualityLeftRule( apply( p, goal, projections ), proof.equation, proof.auxFormula, cx ) )
      case proof @ EqualityRightRule( p, _, _, cx ) =>
        apply( p, goal, projections + ( proof.auxFormula ->
          EqualityLeftRule( WeakeningLeftRule( projections( proof.mainFormula ), proof.equation ), proof.equation, proof.mainFormula, cx ) ) )
      case proof @ AndLeftRule( p, _, _ ) =>
        AndLeftMacroRule( apply( p, goal, projections ), proof.leftConjunct, proof.rightConjunct )
      case proof @ OrLeftRule( p1, _, p2, _ ) =>
        ContractionMacroRule( OrLeftRule( apply( p1, goal, projections ), proof.leftDisjunct, apply( p2, goal, projections ), proof.rightDisjunct ) )
      case proof @ ImpLeftRule( p1, _, p2, _ ) =>
        val q2 = apply( p2, goal, projections )
        if ( !q2.conclusion.antecedent.contains( proof.impConclusion ) ) q2 else {
          val leftGoal = goal | proof.impPremise
          val q1 = apply( p1, leftGoal, Map() ++
            projections.mapValues( pr => CutRule( pr, OrRightMacroRule( LogicalAxiom( goal ), goal, proof.impPremise ), goal ) ) +
            ( proof.impPremise -> OrRightMacroRule( LogicalAxiom( proof.impPremise ), goal, proof.impPremise ) ) )
          ContractionMacroRule( CutRule( q1, OrLeftRule(
            LogicalAxiom( goal ),
            ImpLeftRule( LogicalAxiom( proof.impPremise ), proof.impPremise, q2, proof.impConclusion ), leftGoal ), leftGoal ) )
        }
      case proof @ NegLeftRule( p, _ ) =>
        val auxF = proof.auxFormulas.head.head
        val newGoal = goal | auxF
        val q = apply( p, newGoal, Map() ++
          projections.mapValues( pr => CutRule( pr, OrRightMacroRule( LogicalAxiom( goal ), goal, auxF ), goal ) ) +
          ( auxF -> OrRightMacroRule( LogicalAxiom( auxF ), goal, auxF ) ) )
        ContractionMacroRule( CutRule( q, OrLeftRule(
          LogicalAxiom( goal ),
          NegLeftRule( LogicalAxiom( auxF ), auxF ), newGoal ), newGoal ) )
      case proof @ AndRightRule( p1, _, p2, _ ) =>
        val leftGoal = goal | proof.leftConjunct
        val q1 = apply( p1, leftGoal, Map() ++
          projections.mapValues( pr => CutRule( pr, OrRightMacroRule( LogicalAxiom( goal ), goal, proof.leftConjunct ), goal ) ) +
          ( proof.leftConjunct -> OrRightMacroRule( LogicalAxiom( proof.leftConjunct ), goal, proof.leftConjunct ) ) )
        val q2 = apply( p2, goal, Map() ++
          projections +
          ( proof.rightConjunct -> ContractionMacroRule( CutRule(
            AndRightRule(
              LogicalAxiom( proof.leftConjunct ),
              LogicalAxiom( proof.rightConjunct ), proof.mainFormula ),
            projections( proof.mainFormula ), proof.mainFormula ) ) ) )
        ContractionMacroRule( CutRule( q1, OrLeftRule( LogicalAxiom( goal ), q2, leftGoal ), leftGoal ) )
      case proof @ OrRightRule( p1, _, _ ) =>
        apply( p1, goal, projections +
          ( proof.leftDisjunct ->
            CutRule(
              OrRightMacroRule( LogicalAxiom( proof.leftDisjunct ), proof.leftDisjunct, proof.rightDisjunct ),
              projections( proof.mainFormula ), proof.mainFormula ) ) +
              ( proof.rightDisjunct ->
                CutRule(
                  OrRightMacroRule( LogicalAxiom( proof.rightDisjunct ), proof.leftDisjunct, proof.rightDisjunct ),
                  projections( proof.mainFormula ), proof.mainFormula ) ) )
      case proof @ ExistsRightRule( p, _, _, _, _ ) =>
        val auxF = proof.auxFormulas.head.head
        apply( p, goal, projections + ( auxF ->
          CutRule(
            ExistsRightRule( LogicalAxiom( auxF ), proof.mainFormula, proof.term ),
            projections( proof.mainFormula ), proof.mainFormula ) ) )
      case proof @ ExistsLeftRule( p, _, _, _ ) =>
        ExistsLeftRule( apply( p, goal, projections ), proof.mainFormula, proof.eigenVariable )
      case proof @ ForallLeftRule( p, _, _, _, _ ) =>
        ContractionMacroRule( ForallLeftRule( apply( p, goal, projections ), proof.mainFormula, proof.term ) )
      case proof @ NegRightRule( p, _ ) =>
        require( p.conclusion.succedent.isEmpty )
        CutRule(
          NegRightRule( CutRule( apply( p, Bottom(), Map() ), BottomAxiom, Bottom() ), proof.auxFormulas.head.head ),
          projections( proof.mainFormula ), proof.mainFormula )
      case proof @ ImpRightRule( p, _, _ ) =>
        require( p.conclusion.succedent.size == 1 )
        val q = apply( p, proof.impConclusion, Map( proof.impConclusion -> LogicalAxiom( proof.impConclusion ) ) )
        CutRule( ImpRightMacroRule( q, proof.impPremise, proof.impConclusion ), projections( proof.mainFormula ), proof.mainFormula )
      case proof @ ForallRightRule( p, _, _, _ ) =>
        require( p.conclusion.succedent.size == 1 )
        val q = apply( p, proof.auxFormula, Map( proof.auxFormula -> LogicalAxiom( proof.auxFormula ) ) )
        CutRule( ForallRightRule( q, proof.mainFormula, proof.eigenVariable ), projections( proof.mainFormula ), proof.mainFormula )
    }
    require( result.conclusion.succedent == Seq( goal ) )
    ContractionMacroRule( result )
  }
}
