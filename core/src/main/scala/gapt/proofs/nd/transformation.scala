package gapt.proofs.nd

import gapt.expr._
import gapt.proofs.{ Ant, Suc }

object friedman {

  /**
   * Applies the Friedman translation fr for a given formula a to a
   * formula.
   *
   * This function replaces every atom occurring in the formula by a
   * disjunction formed by the atom and the formula a. The case of the
   * negation is explained by treating ¬A as an abbreviation for A→⊥
   * The Bottom and Top cases are explained by observing that ⊥∨A and
   * ⊤∨A or equivalent to A and ⊤ respectively.
   *
   * @param formula input formula for the function fr
   * @param a formula that is disjunctively added to the atoms of the input formula
   * @return result of applying fr for a to the input formula
   */
  def fr( formula: Expr, a: Formula ): Formula = {

    formula match {
      case Bottom()     => a
      case Top()        => Top()
      case Atom( x, y ) => Or( Atom( x, y ), a )
      case Neg( f )     => Imp( fr( f, a ), a )
      case And( f, g )  => And( fr( f, a ), fr( g, a ) )
      case Or( f, g )   => Or( fr( f, a ), fr( g, a ) )
      case Imp( f, g )  => Imp( fr( f, a ), fr( g, a ) )
      case Ex( x, f ) => {
        if ( freeVariables( a ).contains( x ) ) {
          val freshVar = rename( x, freeVariables( a ) ++ freeVariables( f ) )
          Ex( freshVar, fr( Substitution( x, freshVar )( f ), a ) )
        } else Ex( x, fr( f, a ) )
      }
      case All( x, f ) => {
        if ( freeVariables( a ).contains( x ) ) {
          val freshVar = rename( x, freeVariables( a ) ++ freeVariables( f ) )
          All( freshVar, fr( Substitution( x, freshVar )( f ), a ) )
        } else All( x, fr( f, a ) )
      }
    }
  }

  /**
   * Applies the Friedman proof transformation for a formula A to a
   * given intuitionistic natural deduction proof.
   *
   * The conclusion of the resulting proof is the Friedman
   * translation fr applied to the original conclusion.
   *
   * @param proof A proof in ND for a sequent Γ :- A, without
   * applications of the excluded middle rule
   * @param a The formula that we instantiate the Friedman translation with
   * @return A proof in ND for the sequent fr(Γ, a) :- fr(A, a)
   */
  def apply( proof: NDProof, a: Formula ): NDProof = {

    proof match {

      case LogicalAxiom( formula ) =>
        LogicalAxiom( fr( formula, a ) )

      case WeakeningRule( subProof, formula ) =>
        WeakeningRule( friedman( subProof, a ), fr( formula, a ) )

      case ContractionRule( subProof, aux1, aux2 ) =>
        ContractionRule( friedman( subProof, a ), aux1, aux2 )

      case AndElim1Rule( subProof ) =>
        AndElim1Rule( friedman( subProof, a ) )

      case AndElim2Rule( subProof ) =>
        AndElim2Rule( friedman( subProof, a ) )

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        AndIntroRule( friedman( leftSubProof, a ), friedman( rightSubProof, a ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        ImpElimRule( friedman( leftSubProof, a ), friedman( rightSubProof, a ) )

      case ImpIntroRule( subProof, aux ) =>
        ImpIntroRule( friedman( subProof, a ), aux )

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        OrElimRule(
          friedman( leftSubProof, a ),
          friedman( middleSubProof, a ),
          aux1,
          friedman( rightSubProof, a ),
          aux2 )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        OrIntro1Rule( friedman( subProof, a ), fr( rightDisjunct, a ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        OrIntro2Rule( friedman( subProof, a ), fr( leftDisjunct, a ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        ImpElimRule( friedman( leftSubProof, a ), friedman( rightSubProof, a ) )

      case NegIntroRule( subProof, aux ) =>
        ImpIntroRule( friedman( subProof, a ), aux )

      case BottomElimRule( subProof, mainFormula ) =>
        ImpElimRule( ImpIntroRule( frAux( mainFormula, a ), a ), friedman( subProof, a ) )

      case TopIntroRule =>
        TopIntroRule

      case ForallElimRule( subProof, term ) =>
        ForallElimRule( friedman( subProof, a ), term )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        val eig =
          if ( a.contains( eigenVariable ) )
            rename( eigenVariable, freeVariables( subProof.conclusion ) ++ freeVariables( a ) )
          else eigenVariable
        ForallIntroRule(
          friedman( Substitution( eigenVariable, eig )( subProof ), a ),
          fr( proof.conclusion( Suc( 0 ) ), a ), eig )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val eig =
          if ( a.contains( eigenVariable ) )
            rename( eigenVariable, freeVariables( rightSubProof.conclusion ) ++ freeVariables( a ) )
          else eigenVariable
        ExistsElimRule(
          friedman( leftSubProof, a ),
          friedman( Substitution( eigenVariable, eig )( rightSubProof ), a ), aux, eig )

      case ExistsIntroRule( subProof, formula, term, v ) =>
        ExistsIntroRule( friedman( subProof, a ), fr( proof.conclusion( Suc( 0 ) ), a ), term )

      case EqualityElimRule( leftSubProof, rightSubProof, formula, variable ) =>
        OrElimRule(
          friedman( leftSubProof, a ),
          EqualityElimRule(
            LogicalAxiom( leftSubProof.conclusion( Suc( 0 ) ) ),
            friedman( rightSubProof, a ) ),
          frAux( proof.conclusion( Suc( 0 ) ), a ) )

      case EqualityIntroRule( term ) =>
        OrIntro1Rule( EqualityIntroRule( term ), a )

      case InductionRule( cases, formula, term ) =>
        InductionRule(
          cases.map( x => {
            var ( proof, eigenVars ) = ( x.proof, x.eigenVars )
            for ( eig <- x.eigenVars ) if ( freeVariables( a ).contains( eig ) ) {
              val sub = Substitution( eig, rename( eig, freeVariables( proof.conclusion ) ++ freeVariables( a ) ) )
              proof = sub( proof )
              eigenVars = sub( eigenVars ).map( { case Var( y, z ) => Var( y, z ) } )
            }
            InductionCase( friedman( proof, a ), x.constructor, x.hypotheses, eigenVars )
          } ),
          if ( freeVariables( a ).contains( formula.variable ) ) {
            val vari = rename( formula.variable, freeVariables( formula ) ++ freeVariables( a ) )
            Abs( vari, fr( BetaReduction.betaNormalize( formula( vari ) ), a ) )
          } else Abs( formula.variable, fr( BetaReduction.betaNormalize( formula( formula.variable ) ), a ) ),
          term )

      case TheoryAxiom( formula ) =>
        TheoryAxiom( fr( formula, a ) )

      case DefinitionRule( subProof, formula ) =>
        DefinitionRule( friedman( subProof, a ), fr( formula, a ) )
    }
  }

  /**
   * Creates a proof of the sequent `a :- fr(formula, a)`.
   */
  def frAux( formula: Formula, a: Formula ): NDProof = {

    formula match {
      case Bottom()     => LogicalAxiom( a )
      case Top()        => WeakeningRule( TopIntroRule, a )
      case Atom( _, _ ) => OrIntro2Rule( LogicalAxiom( a ), formula )
      case Neg( f )     => ImpIntroRule( WeakeningRule( LogicalAxiom( a ), fr( f, a ) ), fr( f, a ) )
      case And( f, g )  => ContractionRule( AndIntroRule( frAux( f, a ), frAux( g, a ) ), a )
      case Or( f, g )   => OrIntro1Rule( frAux( f, a ), fr( g, a ) )
      case Imp( f, g )  => ImpIntroRule( WeakeningRule( frAux( g, a ), fr( f, a ) ), fr( f, a ) )
      case Ex( x, f ) => {
        val ( variable, formula ) =
          if ( freeVariables( a ).contains( x ) ) {
            val freshVar = rename( x, freeVariables( a ) ++ freeVariables( f ) )
            ( freshVar, Substitution( x, freshVar )( f ) )
          } else ( x, f )
        ExistsIntroRule( frAux( formula, a ), fr( formula, a ), variable, variable )
      }
      case All( x, f ) => {
        val ( variable, formula ) =
          if ( freeVariables( a ).contains( x ) ) {
            val freshVar = rename( x, freeVariables( a ) ++ freeVariables( f ) )
            ( freshVar, Substitution( x, freshVar )( f ) )
          } else ( x, f )
        ForallIntroRule( frAux( formula, a ), variable, variable )
      }
    }

  }

}

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
   * Applies the Kolmogorov proof transformation to a given natural
   * deduction proof. The transformation removes all occurences of the
   * excluded middle rule and the botttom elimination rule, and thus
   * the resulting proof is a proof in intuitionistic, minimal logic.
   * The conclusion of the resulting proof is the Kolmogorov
   * trnaslation k applied to the original conclusion.
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
        val And( leftConjunct, rightConjunct ) = subProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( subProof ),
          AndElim1Rule( LogicalAxiom( And( k( leftConjunct ), k( rightConjunct ) ) ) ) )

      case AndElim2Rule( subProof ) =>
        val And( leftConjunct, rightConjunct ) = subProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( subProof ),
          AndElim2Rule( LogicalAxiom( And( k( leftConjunct ), k( rightConjunct ) ) ) ) )

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        introcase( AndIntroRule( kolmogorov( leftSubProof ), kolmogorov( rightSubProof ) ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        val Imp( antecedent, consequent ) = leftSubProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( leftSubProof ),
          ImpElimRule( LogicalAxiom( Imp( k( antecedent ), k( consequent ) ) ), kolmogorov( rightSubProof ) ) )

      case ImpIntroRule( subProof, aux ) =>
        introcase( ImpIntroRule( kolmogorov( subProof ), aux ) )

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        val Or( leftDisjunct, rightDisjunct ) = leftSubProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( leftSubProof ),
          OrElimRule(
            LogicalAxiom(
              Or(
                k( leftDisjunct ),
                k( rightDisjunct ) ) ),
            kolmogorov( middleSubProof ),
            aux1,
            kolmogorov( rightSubProof ),
            aux2 ) )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        introcase( OrIntro1Rule( kolmogorov( subProof ), k( rightDisjunct ) ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        introcase( OrIntro2Rule( kolmogorov( subProof ), k( leftDisjunct ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        introcase(
          NegElimRule( kolmogorov( leftSubProof ), kolmogorov( rightSubProof ) ) )

      case NegIntroRule( subProof, aux ) =>
        NegIntroRule(
          NegElimRule(
            kolmogorov( subProof ),
            NegIntroRule( LogicalAxiom( hof"⊥" ) ) ), aux )

      case BottomElimRule( subProof, mainFormula ) =>
        val Neg( lessnegated ) = k( mainFormula )
        NegIntroRule(
          WeakeningRule(
            NegElimRule(
              kolmogorov( subProof ),
              NegIntroRule( LogicalAxiom( Bottom() ) ) ), lessnegated ),
          lessnegated )

      case TopIntroRule =>
        introcase( TopIntroRule )

      case ForallElimRule( subProof, term ) =>
        val All( variable, formula ) = subProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( subProof ),
          ForallElimRule( LogicalAxiom( All( variable, k( formula ) ) ), term ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        introcase(
          ForallIntroRule(
            kolmogorov( subProof ),
            eigenVariable,
            quantifiedVariable ) )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val Ex( variable, formula ) = leftSubProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( leftSubProof ),
          ExistsElimRule(
            LogicalAxiom( Ex( variable, k( formula ) ) ),
            kolmogorov( rightSubProof ),
            aux,
            eigenVariable ) )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        introcase(
          ExistsIntroRule(
            kolmogorov( subProof ),
            k( formula ),
            term,
            variable ) )

      case EqualityElimRule( leftSubProof, rightSubProof, formula, variable ) =>
        val equation = leftSubProof.conclusion( Suc( 0 ) )
        elimcase(
          kolmogorov( leftSubProof ),
          EqualityElimRule(
            LogicalAxiom( equation ),
            kolmogorov( rightSubProof ),
            k( formula ),
            variable ) )

      case EqualityIntroRule( term ) =>
        introcase( EqualityIntroRule( term ) )

      case InductionRule( cases, formula, term ) =>
        val Abs( variable, _ ) = formula
        InductionRule(
          cases.map {
            x =>
              InductionCase(
                kolmogorov( x.proof ), x.constructor, x.hypotheses, x.eigenVars )
          },
          Abs( variable, k( BetaReduction.betaNormalize( formula( variable ) ) ) ),
          term )

      case TheoryAxiom( formula ) =>
        TheoryAxiom( k( formula ) )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val Neg( lessnegated ) = k( leftSubProof.conclusion( Suc( 0 ) ) )
        val p = LogicalAxiom( lessnegated )
        val right =
          NegIntroRule(
            NegElimRule( kolmogorov( leftSubProof ), p ),
            k( leftSubProof.conclusion( aux1 ) ) )
        val left =
          NegIntroRule(
            NegElimRule( kolmogorov( rightSubProof ), p ),
            k( rightSubProof.conclusion( aux2 ) ) )
        NegIntroRule(
          ContractionRule( NegElimRule( left, right ), lessnegated ),
          lessnegated )

      case DefinitionRule( subProof, formula ) =>
        DefinitionRule( kolmogorov( subProof ), k( formula ) )
    }

  }

  private def introcase( proof: NDProof ): NDProof = {
    val negation = Neg( proof.conclusion( Suc( 0 ) ) )
    NegIntroRule( NegElimRule( LogicalAxiom( negation ), proof ), negation )
  }

  private def elimcase( elimproof: NDProof, conclproof: NDProof ): NDProof = {
    val Neg( lessnegated ) = conclproof.conclusion( Suc( 0 ) )
    NegIntroRule(
      NegElimRule(
        elimproof,
        NegIntroRule(
          NegElimRule( conclproof, LogicalAxiom( lessnegated ) ), Ant( 0 ) ) ),
      lessnegated )
  }

}
