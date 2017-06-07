package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, SequentIndex, Suc, lk, nd }
import at.logic.gapt.proofs.nd._

object LKToND {

  /**
   * Converts a deskolemized LKProof π into a natural deduction proof.
   *
   * @param proof The proof π.
   * @return The natural deduction proof translate(π).
   */
  def apply( proof: LKProof ): NDProof = {
    translate( proof, Some( Suc( 0 ) ) )
  }

  def apply( proof: LKProof, focus: Option[SequentIndex] ): NDProof = {
    translate( proof, focus )
  }

  private def check( nd: NDProof, lk: LKProof, focus: Option[SequentIndex] ) = {
    if ( lk.endSequent.succedent.isEmpty ) {
      assert( ( lk.endSequent.size + 1 ) == nd.endSequent.size )
      assert( nd.endSequent( Suc( 0 ) ) == Bottom() )
    } else {
      assert( lk.endSequent.size == nd.endSequent.size )
      assert( lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) )
      assert( lk.endSequent( focus.get ) == nd.endSequent( Suc( 0 ) ) )
    }
    assert( lk.endSequent.antecedent.forall( nd.endSequent.antecedent.contains( _ ) ) )
    assert( lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x => nd.endSequent.antecedent.contains( Neg( x ) ) ) )
  }

  private def exchange( subProof: NDProof, mainFormula: Formula ): NDProof = {
    if ( mainFormula == subProof.endSequent( Suc( 0 ) ) ) {
      subProof
    } else {
      val negMain = hof"-$mainFormula"
      if ( subProof.endSequent.antecedent.contains( negMain ) ) {
        // Negated main formula in antecedent:
        // Move it using LEM
        val r = subProof.endSequent( Suc( 0 ) )

        val ax1 = nd.LogicalAxiom( mainFormula )

        val pr2 = if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"-$r" ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }

        val i = pr2.endSequent.indexOfPolOption( negMain, Polarity.InAntecedent )
        ExcludedMiddleRule( ax1, Ant( 0 ), pr2, i.get )
      } else {
        // Negated main formula not in antecedent
        // Use BottomElimRule to add main formula to succedent
        val r = subProof.endSequent( Suc( 0 ) )

        if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"-$r" ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }
      }
    }
  }

  private def exchange2( subProof: NDProof, mainFormula: Formula ): NDProof = {
    val negMain = hof"-$mainFormula"
    if ( negMain == subProof.endSequent( Suc( 0 ) ) ) {
      subProof
    } else {
      if ( subProof.endSequent.antecedent.contains( mainFormula ) ) {
        // Negated main formula in antecedent:
        // Move it using LEM
        val r = subProof.endSequent( Suc( 0 ) )

        val ax1 = nd.LogicalAxiom( negMain )

        val pr2 = if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, negMain )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"-$r" ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, negMain ) ).
            qed
        }

        val i = pr2.endSequent.indexOfPolOption( mainFormula, Polarity.InAntecedent )
        ExcludedMiddleRule( pr2, i.get, ax1, Ant( 0 ) )
      } else {
        // Main formula not in antecedent
        // Use BottomElimRule to add negated main formula to succedent
        val r = subProof.endSequent( Suc( 0 ) )

        if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, negMain )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"-$r" ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, negMain ) ).
            qed
        }
      }
    }
  }

  private def exchange3( subProof: NDProof, mainFormula: Formula ): NDProof = {
    if ( mainFormula == subProof.endSequent( Suc( 0 ) ) ) {
      subProof
    } else {
      val negMain = hof"-$mainFormula"
      if ( subProof.endSequent.antecedent.contains( negMain ) ) {
        // Negated main formula in antecedent:
        // Move it using LEM
        val Neg( r ) = subProof.endSequent( Suc( 0 ) )

        val ax1 = nd.LogicalAxiom( mainFormula )

        val pr2 = if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"$r" ) ).
            u( NegElimRule( subProof, _ ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }

        val i = pr2.endSequent.indexOfPolOption( negMain, Polarity.InAntecedent )
        ExcludedMiddleRule( ax1, Ant( 0 ), pr2, i.get )
      } else {
        // Negated main formula not in antecedent
        // Use BottomElimRule to add main formula to succedent
        val Neg( r ) = subProof.endSequent( Suc( 0 ) )

        if ( subProof.endSequent( Suc( 0 ) ) == hof"⊥" ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          nd.ProofBuilder.
            c( nd.LogicalAxiom( hof"$r" ) ).
            u( NegElimRule( subProof, _ ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }
      }
    }
  }

  private def translate( proof: LKProof, focus: Option[SequentIndex] ): NDProof = {

    if ( focus != None )
      assert( focus.get.isSuc )

    val ndProof = proof match {

      // Axioms
      case lk.LogicalAxiom( f ) =>
        nd.LogicalAxiom( f )

      case lk.ProofLink( _, seq ) =>
        nd.TheoryAxiom( seq( Suc( 0 ) ), seq.antecedent )

      case ReflexivityAxiom( s ) =>
        nd.EqualityIntroRule( s )

      case TopAxiom =>
        nd.TopIntroRule()

      case BottomAxiom =>
        nd.TheoryAxiom( hof"⊥" )

      // Structural rules
      case WeakeningLeftRule( subProof, formula ) =>
        val heuristicIndex = focus
        WeakeningRule( translate( subProof, heuristicIndex ), formula )

      case p @ WeakeningRightRule( subProof, formula ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          // Pick arbitrary focus
          val heuristicIndex = Suc( 0 )
          exchange( WeakeningRule( translate( subProof, Some( heuristicIndex ) ), hof"-$formula" ), p.mainFormula )
        } else {
          // simply weaken with negated formula on the left
          val focusMain = p.endSequent.indexOfPol( p.endSequent( focus.get ), Polarity.InSuccedent )
          WeakeningRule( translate( subProof, Some( focusMain ) ), hof"-$formula" )
        }

      case p @ ContractionLeftRule( subProof, aux1, aux2 ) =>
        val heuristicIndex = focus
        ContractionRule( translate( subProof, heuristicIndex ), p.mainFormula )

      case p @ ContractionRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val l = subProof.endSequent( aux1 )
          val t = translate( subProof, Some( aux1 ) )
          val il = t.endSequent.indexOfPolOption( hof"-$l", Polarity.InAntecedent )
          nd.ProofBuilder.
            c( nd.LogicalAxiom( l ) ).
            c( t ).
            b( ExcludedMiddleRule( _, Ant( 0 ), _, il.get ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, Some( aux1 ) )

        val tr = translate( rightSubProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) ) else None )

        val i = tr.endSequent.indexOfPol( rightSubProof.endSequent( aux2 ), Polarity.InAntecedent )

        val partialProof = nd.ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          qed

        if ( p.endSequent.succedent.nonEmpty ) {
          exchange( partialProof, p.endSequent( focus.get ) )
        } else {
          partialProof
        }

      // Propositional rules
      case p @ NegLeftRule( subProof, aux ) =>
        val Neg( a ) = p.mainFormula
        val focusMain = subProof.endSequent.indexOfPol( a, Polarity.InSuccedent )
        val t = nd.ProofBuilder.
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( translate( subProof, Some( focusMain ) ) ).
          b( NegElimRule( _, _ ) ).
          qed
        if ( p.endSequent.succedent.nonEmpty )
          exchange( t, p.endSequent( focus.get ) )
        else
          t

      case p @ NegRightRule( subProof, aux ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          // TODO: Can this be done better?
          val heuristicIndex = Suc( 0 )
          val Neg( a ) = p.mainFormula
          val t = translate( subProof, Some( heuristicIndex ) )
          NegIntroRule( exchange( t, Bottom() ), a )
          //val t2 = NegElimRule( nd.LogicalAxiom( Neg( t.endSequent( Suc( 0 ) ) ) ), t )
          //NegIntroRule( t2, a )
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case p @ AndLeftRule( subProof, aux1, aux2 ) =>

        val t = translate( subProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getSequentConnector.parent( focus.get ) ) else None )

        val And( a, b ) = p.mainFormula

        val ax = nd.LogicalAxiom( p.mainFormula )
        nd.ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, a ) ).
          c( ax ).
          u( AndElim1Rule( _ ) ).
          b( ImpElimRule( _, _ ) ).
          u( ImpIntroRule( _, b ) ).
          c( ax ).
          u( AndElim2Rule( _ ) ).
          b( ImpElimRule( _, _ ) ).
          u( ContractionRule( _, p.mainFormula ) ).qed

      case p @ AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val tl = translate( leftSubProof, Some( aux1 ) )
          val tr = translate( rightSubProof, Some( aux2 ) )

          AndIntroRule( tl, tr )
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getLeftSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) ) else None )
        val wtl = if ( p.endSequent.succedent.nonEmpty && p.getLeftSequentConnector.parentOption( focus.get ) == None ) {
          exchange( WeakeningRule( tl, Neg( p.endSequent( focus.get ) ) ), p.endSequent( focus.get ) )
        } else tl

        val tr = translate( rightSubProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) ) else None )
        val wtr = if ( p.endSequent.succedent.nonEmpty && p.getRightSequentConnector.parentOption( focus.get ) == None ) {
          exchange( WeakeningRule( tr, Neg( p.endSequent( focus.get ) ) ), p.endSequent( focus.get ) )
        } else tr

        OrElimRule( nd.LogicalAxiom( p.mainFormula ), wtl, wtr )

      case p @ OrRightRule( subProof1 @ WeakeningRightRule( subProof2, f ), aux1, aux2 ) if f == subProof1.endSequent( aux1 ) || f == subProof1.endSequent( aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Or( a, b ) = p.mainFormula
          f match {
            case `b` =>
              val i = subProof1.getSequentConnector.parent( aux1 )
              nd.ProofBuilder.
                c( translate( subProof2, Some( i ) ) ).
                u( OrIntro1Rule( _, f ) ).
                qed
            case `a` =>
              val i = subProof1.getSequentConnector.parent( aux2 )
              nd.ProofBuilder.
                c( translate( subProof2, Some( i ) ) ).
                u( OrIntro2Rule( _, f ) ).
                qed
          }
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case p @ OrRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Or( a, b ) = p.mainFormula
          val rp = nd.ProofBuilder.
            c( translate( subProof, Some( aux2 ) ) ).
            u( OrIntro2Rule( _, a ) ).
            qed

          val lp = nd.ProofBuilder.
            c( nd.LogicalAxiom( a ) ).
            u( OrIntro1Rule( _, b ) ).
            qed

          val i = rp.endSequent.indexOfPol( Neg( a ), Polarity.InAntecedent )
          ExcludedMiddleRule( lp, Ant( 0 ), rp, i )
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, Some( aux1 ) )

        val tr = translate( rightSubProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) ) else None )

        val Imp( _, b ) = p.mainFormula
        val i = tr.endSequent.indexOfPol( b, Polarity.InAntecedent )

        val partialProof = nd.ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          b( ImpElimRule( _, _ ) ).
          qed

        if ( p.endSequent.succedent.nonEmpty ) {
          exchange( partialProof, p.endSequent( focus.get ) )
        } else {
          partialProof
        }

      case p @ ImpRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Imp( a, _ ) = p.mainFormula
          nd.ProofBuilder.
            c( translate( subProof, Some( aux2 ) ) ).
            u( ImpIntroRule( _, a ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      // Quantifier rules
      case p @ ForallLeftRule( subProof, aux, a: Formula, term: Expr, v: Var ) =>

        val t = translate( subProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getSequentConnector.parent( focus.get ) ) else None )

        val i = t.endSequent.indexOfPol( Substitution( v, term )( a ), Polarity.InAntecedent )
        nd.ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          u( ForallElimRule( _, term ) ).
          b( ImpElimRule( _, _ ) ).
          qed

      case p @ ForallRightRule( subProof, aux, eigen, _ ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          nd.ProofBuilder.
            c( translate( subProof, Some( aux ) ) ).
            u( ForallIntroRule( _, p.mainFormula, eigen ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
        ???

      case p @ ExistsLeftRule( subProof, aux, eigen, v ) =>

        val t = translate( subProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getSequentConnector.parent( focus.get ) ) else None )

        val Ex( _, a ) = p.mainFormula
        val i = t.endSequent.indexOfPol( Substitution( v, eigen )( a ), Polarity.InAntecedent )
        nd.ProofBuilder.
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( t ).
          b( ExistsElimRule( _, _, i, eigen ) ).
          qed

      case ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
        ???

      case p @ ExistsRightRule( subProof, aux, _, t, _ ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          nd.ProofBuilder.
            c( translate( subProof, Some( aux ) ) ).
            u( ExistsIntroRule( _, p.mainFormula, t ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      // Equality rules
      case p @ EqualityLeftRule( subProof, eq, aux, replacementContext ) =>

        val t = translate( subProof, if ( p.endSequent.succedent.nonEmpty ) Some( p.getSequentConnector.parent( focus.get ) ) else None )

        val Abs( x, term ) = replacementContext

        nd.ProofBuilder.
          c( nd.LogicalAxiom( subProof.endSequent( eq ) ) ).
          c( t ).
          u( exchange2( _, subProof.endSequent( aux ) ) ).
          b( EqualityElimRule( _, _, Neg( term.asInstanceOf[Formula] ), x ) ).
          u( ContractionRule( _, subProof.endSequent( eq ) ) ).
          u( exchange3( _, t.endSequent( Suc( 0 ) ) ) ).
          qed

      case p @ EqualityRightRule( subProof, eq, aux, replacementContext ) =>
        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Abs( x, term ) = replacementContext

          nd.ProofBuilder.
            c( nd.LogicalAxiom( subProof.endSequent( eq ) ) ).
            c( translate( subProof, Some( aux ) ) ).
            b( EqualityElimRule( _, _, term.asInstanceOf[Formula], x ) ).
            u( ContractionRule( _, subProof.endSequent( eq ) ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), p.endSequent( focus.get ) )
        }

      case InductionRule( cases, formula, term ) =>
        val ndCases = cases.map {
          case lk.InductionCase( proof, constructor, hypotheses, eigenVars, conclusion ) =>
            nd.InductionCase( translate( proof, Some( conclusion ) ), constructor, hypotheses, eigenVars )
        }
        nd.InductionRule( ndCases, formula, term )

      case DefinitionLeftRule( subProof, aux, main ) =>
        ???

      case DefinitionRightRule( subProof, aux, main ) =>
        ???
    }
    check( ndProof, proof, focus )
    ndProof
  }
}