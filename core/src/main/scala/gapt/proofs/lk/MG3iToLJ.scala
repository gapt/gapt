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
    def withAddGoal( p: LKProof, addGoal: Formula, r: LKProof ): LKProof =
      if ( p.conclusion.succedent.forall( _ == addGoal ) ) {
        val q = apply( p, addGoal, Map( addGoal -> LogicalAxiom( addGoal ) ) )
        val res = ContractionMacroRule( CutRule( q, r, addGoal ) )
        if ( res.conclusion.succedent.isEmpty ) WeakeningRightRule( res, goal ) else res
      } else {
        val newGoal = goal | addGoal
        val q = apply( p, newGoal, Map() ++
          projections.mapValues( pr => CutRule( pr, OrRightMacroRule( LogicalAxiom( goal ), goal, addGoal ), goal ) ) +
          ( addGoal -> OrRightMacroRule( LogicalAxiom( addGoal ), goal, addGoal ) ) )
        ContractionMacroRule( CutRule( q, OrLeftRule( LogicalAxiom( goal ), r, newGoal ), newGoal ) )
      }
    def rightChain( relativeProjs: ( Formula, LKProof )* ): Map[Formula, LKProof] =
      projections ++ relativeProjs.map {
        case ( f, pr ) =>
          val Seq( g ) = pr.conclusion.succedent
          f -> ContractionMacroRule( CutRule( pr, projections( g ), g ) )
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
        if ( !q2.conclusion.antecedent.contains( proof.cutFormula ) ) q2
        else withAddGoal( p1, proof.cutFormula, q2 )
      case BottomAxiom => WeakeningRightRule( BottomAxiom, goal )
      case TopAxiom    => CutRule( TopAxiom, projections( Top() ), Top() )
      case proof @ EqualityLeftRule( p, _, _, cx ) =>
        EqualityLeftRule( apply( p, goal, projections ), proof.equation, proof.auxFormula, cx )
      case proof @ EqualityRightRule( p, _, _, cx ) =>
        apply( p, goal, projections + ( proof.auxFormula ->
          EqualityLeftRule( WeakeningLeftRule( projections( proof.mainFormula ), proof.equation ), proof.equation, proof.mainFormula, cx ) ) )
      case proof @ AndLeftRule( p, _, _ ) =>
        AndLeftMacroRule( apply( p, goal, projections ), proof.leftConjunct, proof.rightConjunct )
      case proof @ OrLeftRule( p1, _, p2, _ ) =>
        OrLeftRule( apply( p1, goal, projections ), proof.leftDisjunct, apply( p2, goal, projections ), proof.rightDisjunct )
      case proof @ ImpLeftRule( p1, _, p2, _ ) =>
        val q2 = apply( p2, goal, projections )
        if ( !q2.conclusion.antecedent.contains( proof.impConclusion ) ) q2
        else withAddGoal( p1, proof.impPremise, ImpLeftRule( LogicalAxiom( proof.impPremise ), proof.impPremise, q2, proof.impConclusion ) )
      case proof @ NegLeftRule( p, _ ) =>
        val auxF = proof.auxFormulas.head.head
        withAddGoal( p, auxF, NegLeftRule( LogicalAxiom( auxF ), auxF ) )
      case proof @ AndRightRule( p1, _, p2, _ ) =>
        val q2 = apply( p2, goal, rightChain( proof.rightConjunct ->
          AndRightRule( LogicalAxiom( proof.leftConjunct ), LogicalAxiom( proof.rightConjunct ), proof.mainFormula ) ) )
        withAddGoal( p1, proof.leftConjunct, q2 )
      case proof @ OrRightRule( p1, _, _ ) =>
        apply( p1, goal, rightChain(
          proof.leftDisjunct ->
            OrRightMacroRule( LogicalAxiom( proof.leftDisjunct ), proof.leftDisjunct, proof.rightDisjunct ),
          proof.rightDisjunct ->
            OrRightMacroRule( LogicalAxiom( proof.rightDisjunct ), proof.leftDisjunct, proof.rightDisjunct ) ) )
      case proof @ ExistsRightRule( p, _, _, _, _ ) =>
        val auxF = proof.auxFormulas.head.head
        apply( p, goal, rightChain( auxF ->
          ExistsRightRule( LogicalAxiom( auxF ), proof.mainFormula, proof.term ) ) )
      case proof @ ExistsLeftRule( p, _, _, _ ) =>
        ExistsLeftRule( apply( p, goal, projections ), proof.mainFormula, proof.eigenVariable )
      case proof @ ForallLeftRule( p, _, _, _, _ ) =>
        ForallLeftRule( apply( p, goal, projections ), proof.mainFormula, proof.term )
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
    require( result.conclusion.succedent.distinct == Seq( goal ) )
    ContractionMacroRule( result )
  }
}
