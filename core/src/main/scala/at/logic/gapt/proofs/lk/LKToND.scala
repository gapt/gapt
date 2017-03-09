package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, SequentIndex, Suc, lk, nd }
import at.logic.gapt.proofs.nd._

object LKToND {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   *
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The natural deduction proof translate(π).
   */
  def apply( proof: LKProof ): NDProof = {
    translate( proof, Suc( 0 ) )
  }

  def apply( proof: LKProof, focus: SequentIndex ): NDProof = {
    translate( proof, focus )
  }

  def check( nd: NDProof, lk: LKProof, focus: SequentIndex ) = {
    if ( lk.endSequent.succedent.isEmpty ) {
      assert( ( lk.endSequent.size + 1 ) == nd.endSequent.size )
      assert( nd.endSequent( Suc( 0 ) ) == Bottom() )
    } else {
      assert( lk.endSequent.size == nd.endSequent.size )
      assert( lk.endSequent.succedent.contains( nd.endSequent( Suc( 0 ) ) ) )
      assert( lk.endSequent( focus ) == nd.endSequent( Suc( 0 ) ) )
    }
    assert( lk.endSequent.antecedent.forall( nd.endSequent.antecedent.contains( _ ) ) )
    assert( lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x => nd.endSequent.antecedent.contains( Neg( x ) ) ) )
  }

  private def exchange( subProof: NDProof, mainFormula: HOLFormula ): NDProof = {
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

  private def translate( proof: LKProof, focus: SequentIndex ): NDProof = {

    assert( focus.isSuc )

    val ndProof = proof match {

      // Axioms
      case lk.LogicalAxiom( atom: HOLAtom ) =>
        nd.LogicalAxiom( atom )

      case ReflexivityAxiom( s ) =>
        ???

      case TopAxiom =>
        ???

      case BottomAxiom =>
        ???

      case TheoryAxiom( sequent ) =>
        ???

      // Structural rules
      case WeakeningLeftRule( subProof, formula ) =>
        val heuristicIndex = focus
        WeakeningRule( translate( subProof, heuristicIndex ), formula )

      case p @ WeakeningRightRule( subProof, formula ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          // Pick arbitrary focus
          val heuristicIndex = Suc( 0 )
          exchange( WeakeningRule( translate( subProof, heuristicIndex ), hof"-$formula" ), p.mainFormula )
        } else {
          // TODO OPTIMIZATION: exchanging twice should not be required
          // simply weaken with negated formula on the left
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ ContractionLeftRule( subProof, aux1, aux2 ) =>
        val heuristicIndex = focus
        ContractionRule( translate( subProof, heuristicIndex ), p.mainFormula )

      case p @ ContractionRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val l = subProof.endSequent( aux1 )
          val t = translate( subProof, aux1 )
          val il = t.endSequent.indexOfPolOption( hof"-$l", Polarity.InAntecedent )
          nd.ProofBuilder.
            c( nd.LogicalAxiom( l ) ).
            c( t ).
            b( ExcludedMiddleRule( _, Ant( 0 ), _, il.get ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, aux1 )

        val tr =
          if ( p.endSequent.succedent.nonEmpty ) {
            p.getRightSequentConnector.parentOption( focus ) match {
              case Some( ir ) =>
                translate( rightSubProof, ir )
              case None =>
                val heuristicFocus = Suc( 0 )
                translate( rightSubProof, heuristicFocus )
            }
          } else {
            val heuristicFocus = Suc( 0 )
            translate( rightSubProof, heuristicFocus )
          }

        val i = tr.endSequent.indexOfPol( rightSubProof.endSequent( aux2 ), Polarity.InAntecedent )
        exchange(
          nd.ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          qed, p.endSequent( focus )
        )

      // Propositional rules
      case p @ NegLeftRule( subProof, aux ) =>
        val Neg( a ) = p.mainFormula
        val focusMain = subProof.endSequent.indexOfPol( a, Polarity.InSuccedent )
        val t = nd.ProofBuilder.
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( translate( subProof, focusMain ) ).
          b( NegElimRule( _, _ ) ).
          qed
        if ( p.endSequent.succedent.nonEmpty )
          exchange( t, p.endSequent( focus ) )
        else
          t

      case p @ NegRightRule( subProof, aux ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val heuristicIndex = Suc( 0 )
          val Neg( a ) = p.mainFormula
          val t = translate( subProof, heuristicIndex )
          NegIntroRule( exchange( t, Bottom() ), a )
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ AndLeftRule( subProof, aux1, aux2 ) =>
        val t = translate( subProof, p.getSequentConnector.parent( focus ) )

        val And( a, b ) = p.mainFormula

        val ax = nd.LogicalAxiom( p.mainFormula )
        val p1 = AndElim1Rule( ax )
        val p2 = AndElim2Rule( ax )

        val q1 = ImpIntroRule( t, a )
        val q2 = ImpElimRule( q1, p1 )
        val q3 = ImpIntroRule( q2, b )
        val q4 = ImpElimRule( q3, p2 )
        ContractionRule( q4, p.mainFormula )

      case p @ AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val tl = translate( leftSubProof, aux1 )
          val tr = translate( rightSubProof, aux2 )

          AndIntroRule( tl, tr )
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl =
          if ( p.endSequent.succedent.nonEmpty ) {
            p.getLeftSequentConnector.parentOption( focus ) match {
              case Some( il ) =>
                translate( leftSubProof, il )
              case None =>
                val heuristicFocus = Suc( 0 )
                val t = WeakeningRule( translate( leftSubProof, heuristicFocus ), Neg( p.endSequent( focus ) ) )
                exchange( t, p.endSequent( focus ) )
            }
          } else {
            val heuristicFocus = Suc( 0 )
            translate( leftSubProof, heuristicFocus )
          }

        val tr =
          if ( p.endSequent.succedent.nonEmpty ) {
            p.getRightSequentConnector.parentOption( focus ) match {
              case Some( ir ) =>
                translate( rightSubProof, ir )
              case None =>
                val heuristicFocus = Suc( 0 )
                val t = WeakeningRule( translate( rightSubProof, heuristicFocus ), Neg( p.endSequent( focus ) ) )
                exchange( t, p.endSequent( focus ) )
            }
          } else {
            val heuristicFocus = Suc( 0 )
            translate( rightSubProof, heuristicFocus )
          }

        OrElimRule( tl, tr, nd.LogicalAxiom( p.mainFormula ) )

      case p @ OrRightRule( subProof1 @ WeakeningRightRule( subProof2, f ), aux1, aux2 ) if f == subProof1.endSequent( aux1 ) || f == subProof1.endSequent( aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val Or( a, b ) = p.mainFormula
          f match {
            case `b` =>
              val i = subProof1.getSequentConnector.parent( aux1 )
              nd.ProofBuilder.
                c( translate( subProof2, i ) ).
                u( OrIntro1Rule( _, f ) ).
                qed
            case `a` =>
              val i = subProof1.getSequentConnector.parent( aux2 )
              nd.ProofBuilder.
                c( translate( subProof2, i ) ).
                u( OrIntro2Rule( _, f ) ).
                qed
          }
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ OrRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val Or( a, b ) = p.mainFormula
          val rp = nd.ProofBuilder.
            c( translate( subProof, aux2 ) ).
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
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, aux1 )

        val tr =
          if ( p.endSequent.succedent.nonEmpty ) {
            p.getRightSequentConnector.parentOption( focus ) match {
              case Some( ir ) =>
                translate( rightSubProof, ir )
              case None =>
                val heuristicFocus = Suc( 0 )
                translate( rightSubProof, heuristicFocus )
            }
          } else {
            val heuristicFocus = Suc( 0 )
            translate( rightSubProof, heuristicFocus )
          }

        val Imp( _, b ) = p.mainFormula
        val i = tr.endSequent.indexOfPol( b, Polarity.InAntecedent )

        exchange(
          nd.ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          b( ImpElimRule( _, _ ) ).
          qed, p.endSequent( focus )
        )

      case p @ ImpRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          val Imp( a, _ ) = p.mainFormula
          nd.ProofBuilder.
            c( translate( subProof, aux2 ) ).
            u( ImpIntroRule( _, a ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      // Quantifier rules
      case p @ ForallLeftRule( subProof, aux, a: HOLFormula, term: LambdaExpression, v: Var ) =>

        val t = translate( subProof, p.getSequentConnector.parent( focus ) )

        val i = t.endSequent.indexOfPol( Substitution( v, term )( a ), Polarity.InAntecedent )
        nd.ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          u( ForallElimRule( _, a, term, v ) ).
          b( ImpElimRule( _, _ ) ).
          qed

      case p @ ForallRightRule( subProof, aux, eigen, _ ) =>

        if ( p.mainFormula == p.endSequent( focus ) ) {
          nd.ProofBuilder.
            c( translate( subProof, aux ) ).
            u( ForallIntroRule( _, p.mainFormula, eigen ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
        ???

      case p @ ExistsLeftRule( subProof, aux, eigen, v ) =>

        val t = translate( subProof, p.getSequentConnector.parent( focus ) )

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

        if ( p.mainFormula == p.endSequent( focus ) ) {
          nd.ProofBuilder.
            c( translate( subProof, aux ) ).
            u( ExistsIntroRule( _, p.mainFormula, t ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOfPol( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, focusMain ), p.endSequent( focus ) )
        }

      // Equality rules
      case p: EqualityRule =>
        ???

      case DefinitionLeftRule( subProof, aux, main ) =>
        ???

      case DefinitionRightRule( subProof, aux, main ) =>
        ???
    }
    check( ndProof, proof, focus )
    ndProof
  }

  /*
  private def translate( proof: LKProof, focus: SequentIndex ): NDProof = {

    assert( focus.isSuc )

    val ndProof = proof match {

      // Axioms
      case lk.LogicalAxiom( atom: HOLAtom ) =>
        nd.LogicalAxiom( atom )

      case ReflexivityAxiom( s ) =>
        ???

      case TopAxiom =>
        ???

      case BottomAxiom =>
        ???

      case TheoryAxiom( sequent ) =>
        ???

      // Structural rules
      case WeakeningLeftRule( subProof, formula ) =>
        //translate( subProof, focus )
        val ret = WeakeningRule( translate( subProof, focus ), formula )
        ret

      case p @ WeakeningRightRule( subProof, formula ) =>
        //translate( subProof, focus )
        val ret = p.getSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            WeakeningRule( translate( subProof, i ), hof"-$formula" )
          case None =>
            //exchange( translate( subProof, Suc( 0 ) ), p.endSequent( focus ) )
            // different order as in other rules
            // explicit weakening here? would (exchange o translate) be enough?
            val t = translate( subProof, Suc( 0 ) )
            val ret = exchange( WeakeningRule( t, hof"-$formula" ), p.endSequent( focus ) )
            ret

          //without weakening weakenright/contractright example breaks
          //exchange( translate( subProof, Suc( 0 ) ), p.endSequent( focus ) )
        }
        ret

      case ContractionLeftRule( subProof, aux1, aux2 ) =>
        val l = subProof.endSequent( aux1 )
        val r = subProof.endSequent( aux2 )

        val t = translate( subProof, focus )

        assert( l == r )

        ContractionRule( t, l )

      case ContractionRightRule( subProof, aux1, aux2 ) =>
        val l = subProof.endSequent( aux1 )
        val r = subProof.endSequent( aux2 )

        val t = translate( subProof, aux2 )

        assert( l == r )

        val il = t.endSequent.find { case s if s == hof"-$l" => true; case _ => false }
        ExcludedMiddleRule( nd.LogicalAxiom( l ), Ant( 0 ), t, il.get )

      case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val l = leftSubProof.endSequent( aux1 )

        /*
        val tl = p.getLeftSequentConnector.parentOption( aux1 ) match {
          case Some( i ) =>
            translate( leftSubProof, i )
          case None =>
            exchange( translate( leftSubProof, Suc( 0 ) ), l )
        }
        */
        val tl = translate( leftSubProof, aux1 )

        val tr = p.getRightSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            translate( rightSubProof, i )
          case None =>
            translate( rightSubProof, Suc( 0 ) )
        }

        ImpElimRule( ImpIntroRule( tl, hof"$l" ), tr )

      // Propositional rules
      case NegLeftRule( subProof, aux ) =>
        val r = subProof.endSequent( aux )

        NegElimRule( nd.LogicalAxiom( hof"-$r" ), translate( subProof, aux ) )

      case p @ NegRightRule( subProof, aux ) =>
        val l = subProof.endSequent( aux )
        /*
        val t = exchange( translate( subProof, Ant( 0 ) ), Bottom() )
        */

        // exchanging with bottom in both cases
        val t = p.getSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            exchange( translate( subProof, Suc( 0 ) ), Bottom() )
          case None =>
            ???
          //exchange( translate( subProof, Suc( 0 ) ), Bottom() )
        }

        NegIntroRule( t, l )

      case p @ AndLeftRule( subProof, aux1, aux2 ) =>

        val t = p.getSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            translate( subProof, i )
          case None =>
            translate( subProof, Suc( 0 ) )
        }

        val And( a, b ) = p.mainFormula

        val ax = nd.LogicalAxiom( p.mainFormula )
        val p1 = AndElim1Rule( ax )
        val p2 = AndElim2Rule( ax )

        val q1 = ImpIntroRule( t, a )
        val q2 = ImpElimRule( q1, p1 )
        val q3 = ImpIntroRule( q2, b )
        val q4 = ImpElimRule( q3, p2 )
        ContractionRule( q4, p.mainFormula )

        /*
        val l = subProof.endSequent( aux1 )
        val r = subProof.endSequent( aux2 )

        val ff = proof.endSequent( focus )

        val il = subProof.endSequent.find{ case `ff` => true; case _ => false }
        val t = translate( subProof, il.get )

        val l1 = exchange( t, ff )

        val r1 = LogicalAxiom( hof"$l & $r" )
        // TODO Elim1/Elim2 based on weakening in sub proof
        val r2 = AndElim1Rule
        */
        ???

      case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val tl = translate( leftSubProof, aux1 )
        val tr = translate( rightSubProof, aux2 )

        AndIntroRule( tl, tr )

      case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = p.getLeftSequentConnector.parentOption( focus ) match {
          case Some( il ) =>
            translate( leftSubProof, il )
          case None =>
            // TODO pick new focus heuristically
            //exchange( translate( leftSubProof, Suc( 0 ) ), p.endSequent( focus ) )
            val t = WeakeningRule( translate( leftSubProof, Suc( 0 ) ), Neg( p.endSequent( focus ) ) )
            exchange( t, p.endSequent( focus ) )
        }

        val tr = p.getRightSequentConnector.parentOption( focus ) match {
          case Some( ir ) =>
            translate( rightSubProof, ir )
          case None =>
            // TODO pick new focus heuristically
            //exchange( translate( rightSubProof, Suc( 0 ) ), p.endSequent( focus ) )
            val t = WeakeningRule( translate( rightSubProof, Suc( 0 ) ), Neg( p.endSequent( focus ) ) )
            exchange( t, p.endSequent( focus ) )
        }

        OrElimRule( tl, tr, nd.LogicalAxiom( p.mainFormula ) )

      case p @ OrRightRule( subProof1 @ WeakeningRightRule( subProof2, f ), aux1, aux2 ) if f == subProof1.endSequent( aux1 ) || f == subProof1.endSequent( aux2 ) =>
        val l = subProof1.endSequent( aux1 )
        val r = subProof1.endSequent( aux2 )

        val ret = f match {
          case `r` =>
            val t = subProof1.getSequentConnector.parentOption( aux1 ) match {
              case Some( i ) =>
                translate( subProof2, i )
              case None =>
                ???
              //exchange( translate( subProof2, Suc( 0 ) ), subProof2.endSequent( aux1 ) )
            }
            OrIntro1Rule( t, f )
          case `l` =>
            val t = subProof1.getSequentConnector.parentOption( aux2 ) match {
              case Some( i ) =>
                translate( subProof2, i )
              case None =>
                ???
              //exchange( translate( subProof2, Suc( 0 ) ), subProof2.endSequent( aux2 ) )
            }
            OrIntro2Rule( t, f )
        }
        ret

      case p @ OrRightRule( subProof, aux1, aux2 ) =>
        val Or( l, r ) = p.mainFormula

        val t = translate( subProof, aux2 )
        val lp = OrIntro2Rule( exchange( t, r ), l )
        val rp1 = nd.LogicalAxiom( l )
        val rp2 = OrIntro1Rule( rp1, r )

        val i = lp.endSequent.indexOfPolOption( Neg( l ), Polarity.InAntecedent )
        ExcludedMiddleRule( rp2, Ant( 0 ), lp, i.get )

      case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val l = leftSubProof.endSequent( aux1 )
        val r = rightSubProof.endSequent( aux2 )

        val tl = p.getLeftSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            exchange( translate( leftSubProof, i ), l )
          case None =>
            exchange( translate( leftSubProof, Suc( 0 ) ), l )
        }
        //val tl = translate( leftSubProof, aux1 )

        val tr = p.getRightSequentConnector.parentOption( focus ) match {
          case Some( i ) =>
            // why exchange here?
            //exchange( translate( rightSubProof, i ), p.endSequent( focus ) )
            translate( rightSubProof, i )
          case None =>
            //exchange( translate( rightSubProof, Suc( 0 ) ), p.endSequent( focus ) )
            translate( rightSubProof, Suc( 0 ) )
        }

        val p1 = ImpElimRule( nd.LogicalAxiom( hof"$l -> $r" ), tl )

        val i = tr.endSequent.indexOfPolOption( r, Polarity.InAntecedent )
        val ret = ImpElimRule( ImpIntroRule( tr, i.get ), p1 )
        ret

      case p @ ImpRightRule( subProof, aux1, aux2 ) =>
        val Imp( l, r ) = p.mainFormula

        val t = translate( subProof, aux2 )

        val i = t.endSequent.indexOfPolOption( l, Polarity.InAntecedent )
        val ret = ImpIntroRule( t, i.get )
        ret

      // Quantifier rules
      case ForallLeftRule( subProof, aux, _, t, _ ) =>
        ???

      case ForallRightRule( subProof, aux, eigen, _ ) =>
        ???

      case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
        ???

      case ExistsLeftRule( subProof, aux, eigen, _ ) =>
        ???

      case ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
        ???

      case ExistsRightRule( subProof, aux, _, t, _ ) =>
        ???

      // Equality rules
      case p: EqualityRule =>
        ???

      case DefinitionLeftRule( subProof, aux, main ) =>
        ???

      case DefinitionRightRule( subProof, aux, main ) =>
        ???
    }
    // Check needed for NegLeft with potentially empty succedent
    val ret = if ( proof.endSequent.succedent.nonEmpty ) {
      exchange( ndProof, proof.endSequent( focus ) )
    } else {
      ndProof
    }
    check( ret, proof, focus )
    ret
  }
  */
}