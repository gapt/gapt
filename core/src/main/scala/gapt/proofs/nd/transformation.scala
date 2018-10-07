package gapt.proofs.nd

import gapt.expr._
import gapt.proofs.{ Ant, Suc }

object kolmogorov {

  /**
   * Applies the Kolmogorov translation k to a formula.
   * This function puts a double negation in front of every subformula,
   * in case this subformula is not negated already.
   *
   * @param formula input formula for the function k
   * @return result of applying k to the input formula
   */
  def k( formula: Expr ): Formula = {

    formula match {
      case Bottom()     => doublenegate( Bottom() )
      case Top()        => doublenegate( Top() )
      case Atom( x, y ) => doublenegate( Atom( x, y ) )
      case Neg( f )     => Neg( k( f ) )
      case And( f, g )  => doublenegate( And( k( f ), k( g ) ) )
      case Or( f, g )   => doublenegate( Or( k( f ), k( g ) ) )
      case Imp( f, g )  => doublenegate( Imp( k( f ), k( g ) ) )
      case Ex( x, f )   => doublenegate( Ex( x, k( f ) ) )
      case All( x, f )  => doublenegate( All( x, k( f ) ) )
    }
  }

  private def doublenegate( formula: Formula ): Formula = Neg( Neg( formula ) )

  /**
   * Applies the Kolmogorov proof transformation to a given natural deduction proof.
   * The transformation removes all occurences of the excluded middle rule and the botttom elimination rule,
   * and thus the resulting proof is a proof in intuitionistic, minimal logic.
   * The conclusion of the resulting proof is the Kolmogorov trnaslation k applied to the original conclusion.
   *
   * @param proof A proof in ND for a sequent Γ :- A
   * @return A proof in intuitionistic, minimal ND for the sequent k(Γ) :- k(A)
   */
  def apply( proof: NDProof ): NDProof = {

    proof match {

      case LogicalAxiom( formula ) =>
        LogicalAxiom( k( formula ) )

      case WeakeningRule( subProof, formula ) =>
        WeakeningRule( kolmogorov( subProof ), k( formula ) )

      case ContractionRule( subProof, aux1, aux2 ) =>
        ContractionRule( kolmogorov( subProof ), aux1, aux2 )

      case AndElim1Rule( subProof ) =>
        val ( leftConjunct, rightConjunct ) = subProof.conclusion( Suc( 0 ) ) match { case And( left, right ) => ( left, right ) }
        elimcase(
          kolmogorov( subProof ),
          AndElim1Rule( LogicalAxiom( And( k( leftConjunct ), k( rightConjunct ) ) ) ) )

      case AndElim2Rule( subProof ) =>
        val ( leftConjunct, rightConjunct ) = subProof.conclusion( Suc( 0 ) ) match { case And( left, right ) => ( left, right ) }
        elimcase(
          kolmogorov( subProof ),
          AndElim2Rule( LogicalAxiom( And( k( leftConjunct ), k( rightConjunct ) ) ) ) )

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        introcase( AndIntroRule( kolmogorov( leftSubProof ), kolmogorov( rightSubProof ) ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        val ( antecedent, consequent ) = leftSubProof.conclusion( Suc( 0 ) ) match { case Imp( ant, cons ) => ( ant, cons ) }
        elimcase(
          kolmogorov( leftSubProof ),
          ImpElimRule( LogicalAxiom( Imp( k( antecedent ), k( consequent ) ) ), kolmogorov( rightSubProof ) ) )

      case ImpIntroRule( subProof, aux ) =>
        introcase( ImpIntroRule( kolmogorov( subProof ), aux ) )

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        val ( leftDisjunct, rightDisjunct ) = leftSubProof.conclusion( Suc( 0 ) ) match { case Or( left, right ) => ( left, right ) }
        elimcase(
          kolmogorov( leftSubProof ),
          OrElimRule( LogicalAxiom( Or( k( leftDisjunct ), k( rightDisjunct ) ) ), kolmogorov( middleSubProof ), aux1, kolmogorov( rightSubProof ), aux2 ) )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        introcase( OrIntro1Rule( kolmogorov( subProof ), k( rightDisjunct ) ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        introcase( OrIntro2Rule( kolmogorov( subProof ), k( leftDisjunct ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        introcase( NegElimRule( kolmogorov( leftSubProof ), kolmogorov( rightSubProof ) ) )

      case NegIntroRule( subProof, aux ) =>
        NegIntroRule( NegElimRule( kolmogorov( subProof ), NegIntroRule( LogicalAxiom( hof"⊥" ) ) ), aux )

      case BottomElimRule( subProof, mainFormula ) =>
        val lessnegated = k( mainFormula ) match { case Neg( formula ) => formula }
        NegIntroRule( WeakeningRule( NegElimRule( kolmogorov( subProof ), NegIntroRule( LogicalAxiom( Bottom() ) ) ), lessnegated ), lessnegated )

      case TopIntroRule =>
        introcase( TopIntroRule )

      case ForallElimRule( subProof, term ) =>
        val ( variable, formula ) = subProof.conclusion( Suc( 0 ) ) match { case All( vari, form ) => ( vari, form ) }
        elimcase(
          kolmogorov( subProof ),
          ForallElimRule( LogicalAxiom( All( variable, k( formula ) ) ), term ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        introcase( ForallIntroRule( kolmogorov( subProof ), eigenVariable, quantifiedVariable ) )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val ( variable, formula ) = leftSubProof.conclusion( Suc( 0 ) ) match { case Ex( vari, form ) => ( vari, form ) }
        elimcase(
          kolmogorov( leftSubProof ),
          ExistsElimRule( LogicalAxiom( Ex( variable, k( formula ) ) ), kolmogorov( rightSubProof ), aux, eigenVariable ) )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        introcase( ExistsIntroRule( kolmogorov( subProof ), k( formula ), term, variable ) )

      case EqualityElimRule( leftSubProof, rightSubProof, formula, variable ) =>
        val equation = leftSubProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( leftSubProof ),
          EqualityElimRule( LogicalAxiom( equation ), kolmogorov( rightSubProof ), k( formula ), variable ) )

      case EqualityIntroRule( term ) =>
        introcase( EqualityIntroRule( term ) )

      case InductionRule( cases, formula, term ) =>
        val ( variable, _ ) = formula match { case Abs( vari, form ) => ( vari, form ) }
        InductionRule(
          cases.map( x => InductionCase( kolmogorov( x.proof ), x.constructor, x.hypotheses, x.eigenVars ) ),
          Abs( variable, k( BetaReduction.betaNormalize( formula( variable ) ) ) ),
          term )

      case TheoryAxiom( formula ) =>
        TheoryAxiom( k( formula ) )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val lessnegated = k( leftSubProof.conclusion( Suc( 0 ) ) ) match { case Neg( formula ) => formula }
        val p = LogicalAxiom( lessnegated )
        val left = NegIntroRule( NegElimRule( kolmogorov( leftSubProof ), p ), k( leftSubProof.conclusion( aux1 ) ) )
        val right = NegIntroRule( NegElimRule( kolmogorov( rightSubProof ), p ), k( rightSubProof.conclusion( aux2 ) ) )
        NegIntroRule( ContractionRule( NegElimRule( left, right ), lessnegated ), lessnegated )

      case DefinitionRule( subProof, formula ) =>
        DefinitionRule( kolmogorov( subProof ), k( formula ) )
    }

  }

  private def introcase( proof: NDProof ): NDProof = {
    val negation = Neg( proof.conclusion( Suc( 0 ) ) )
    NegIntroRule( NegElimRule( LogicalAxiom( negation ), proof ), negation )
  }

  private def elimcase( elimproof: NDProof, conclproof: NDProof ): NDProof = {
    val lessnegated = conclproof.conclusion( Suc( 0 ) ) match { case Neg( formula ) => formula }
    NegIntroRule( NegElimRule(
      elimproof,
      NegIntroRule( NegElimRule( conclproof, LogicalAxiom( lessnegated ) ), Ant( 0 ) ) ), lessnegated )
  }

}