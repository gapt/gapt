package gapt.proofs.lk.transformations

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.subst.Substitution
import gapt.proofs.Ant
import gapt.proofs.ProofBuilder
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.lk
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.nd
import gapt.proofs.nd._

object LKToND {

  /**
   * Converts an LKProof π into a natural deduction proof.
   *
   * @param proof The proof π.
   * @param focus The index in the LK succedent of the formula to be proved in the ND proof,
   *              or None if the succedent is empty.
   * @return The natural deduction proof translate(π).
   */

  def apply( proof: LKProof, focus: Option[SequentIndex] = null )( implicit ctx: Context = Context() ): NDProof = {
    translate( proof, focus =
      if ( focus != null ) focus else if ( proof.endSequent.succedent.isEmpty ) None else Some( Suc( 0 ) ) )
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
    assert( lk.endSequent.succedent.filter( _ != nd.endSequent( Suc( 0 ) ) ).forall( x =>
      nd.endSequent.antecedent.contains( Neg( x ) ) ) )
  }

  private def exchange( subProof: NDProof, mainFormula: Option[Formula] ): NDProof =
    mainFormula.map( exchange( subProof, _ ) ).getOrElse( subProof )

  /**
   * Macro rule to exchange a mainFormula (A) with the formula in the succedent (B) in subProof (π).
   *
   * <pre>
   *      (π)
   *  Γ, ¬A :- B
   * ------------- ex ¬A
   *  Γ, ¬B :- A
   * </pre>
   *
   * @param subProof The proof π.
   * @param mainFormula The formula ¬A.
   * @return The natural deduction proof after exchanging ¬A and B.
   */
  private def exchange( subProof: NDProof, mainFormula: Formula ): NDProof = {
    if ( mainFormula == subProof.endSequent( Suc( 0 ) ) ) {
      subProof
    } else {
      val negMain = -mainFormula
      if ( subProof.endSequent.antecedent.contains( negMain ) ) {
        // Negated main formula in antecedent:
        // Move it using LEM
        val r = subProof.endSequent( Suc( 0 ) )

        val ax1 = nd.LogicalAxiom( mainFormula )

        val pr2 = if ( subProof.endSequent( Suc( 0 ) ) == Bottom() ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          ProofBuilder.
            c( nd.LogicalAxiom( -r ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }

        val i = pr2.endSequent.indexOfOption( negMain, Polarity.InAntecedent )
        ExcludedMiddleRule( ax1, Ant( 0 ), pr2, i.get )
      } else {
        // Negated main formula not in antecedent
        // Use BottomElimRule to add main formula to succedent
        val r = subProof.endSequent( Suc( 0 ) )

        if ( subProof.endSequent( Suc( 0 ) ) == Bottom() ) {
          BottomElimRule( subProof, mainFormula )
        } else {
          ProofBuilder.
            c( nd.LogicalAxiom( -r ) ).
            u( NegElimRule( _, subProof ) ).
            u( BottomElimRule( _, mainFormula ) ).
            qed
        }
      }
    }
  }

  private def heuristicIndex( proof: LKProof ) =
    if ( proof.endSequent.succedent.isEmpty ) None else Some( Suc( 0 ) )

  private def translate( proof: LKProof, focus: Option[SequentIndex] )( implicit ctx: Context ): NDProof = {

    assert( focus.forall( _ => proof.endSequent.succedent.nonEmpty ) )
    assert( focus.forall( _.isSuc ) )

    // Optimization when the end-sequent has the form :- ¬A, A with focus ¬A, then just return ¬A :- ¬A
    focus match {
      case Some( i ) =>
        proof.endSequent( i ) match {
          case Neg( f ) if ( proof.endSequent.size == 2 && proof.endSequent.delete( i ).forall( _ == f ) ) => return nd.LogicalAxiom( Neg( f ) )
          case _ => ()
        }
      case _ => ()
    }

    val ndProof = proof match {

      // Axioms
      case lk.rules.LogicalAxiom( f ) =>
        nd.LogicalAxiom( f )

      case lk.rules.ProofLink( prf, seq ) =>
        val Apps( Const( proofName, _, _ ), args ) = prf
        val ( genprf, genseq ) = ctx.get[ProofNames].names( proofName )
        val Apps( _, vs ) = genprf

        def handleSuccedent( seq: Vector[Formula], toProve: Formula ): NDProof = {
          if ( seq.size == 1 ) {
            ProofBuilder.
              c( nd.LogicalAxiom( -seq.last ) ).
              c( nd.LogicalAxiom( seq.last ) ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, toProve ) ).
              qed
          } else {
            ProofBuilder.
              c( nd.LogicalAxiom( -seq.last ) ).
              c( nd.LogicalAxiom( Or( seq ) ) ).
              c( handleSuccedent( seq.reverse.tail.reverse, seq.last ) ).
              c( nd.LogicalAxiom( seq.last ) ).
              t( OrElimRule( _, _, _ ) ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, toProve ) ).
              qed
          }
        }

        val t = ProofBuilder.
          c( nd.TheoryAxiom( All.Block( vs.asInstanceOf[List[Var]], genseq.toImplication ) ) ).
          u( nd.ForallElimBlock( _, args ) ).
          c( nd.LogicalAxiom( seq( Ant( 0 ) ) ) ).
          u( seq.antecedent.tail.foldLeft( _ )( ( a, b ) => AndIntroRule( a, nd.LogicalAxiom( b ) ) ) ).
          b( ImpElimRule( _, _ ) ).
          qed
        val tsuc = if ( seq.succedent.size > 1 ) {
          ProofBuilder.
            c( t ).
            c( handleSuccedent( seq.succedent.reverse.tail.reverse, seq.succedent.last ) ).
            c( nd.LogicalAxiom( seq.succedent.last ) ).
            t( OrElimRule( _, _, _ ) ).
            qed
        } else t

        exchange( tsuc, focus.map( seq.apply ) )

      case ReflexivityAxiom( s ) =>
        nd.EqualityIntroRule( s )

      case TopAxiom =>
        nd.TopIntroRule

      case BottomAxiom =>
        nd.LogicalAxiom( Bottom() )

      // Structural rules
      case WeakeningLeftRule( subProof, formula ) =>
        WeakeningRule( translate( subProof, focus ), formula )

      case p @ WeakeningRightRule( subProof, formula ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          // Pick arbitrary focus
          val ndProof = translate( subProof, heuristicIndex( subProof ) )
          // This check solves a bug that occured when WeakeningRightRule
          // was applied after BottomAxiom (cf. classical pairing test case)
          if ( proof.endSequent.forall( f => proof.endSequent.filter( _ == f ).size ==
            ndProof.endSequent.filter( _ == f ).size ) )
            ndProof
          else
            exchange( WeakeningRule( ndProof, -formula ), p.mainFormula )
        } else {
          // simply weaken with negated formula on the left
          WeakeningRule( translate( subProof, focus.map( p.getSequentConnector.parent ) ), -formula )
        }

      case p @ ContractionLeftRule( subProof, aux1, aux2 ) =>
        ContractionRule( translate( subProof, focus ), p.mainFormula )

      case p @ ContractionRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val l = subProof.endSequent( aux1 )
          val t = translate( subProof, Some( aux1 ) )
          val il = t.endSequent.indexOf( -l, Polarity.InAntecedent )
          ProofBuilder.
            c( nd.LogicalAxiom( l ) ).
            c( t ).
            b( ExcludedMiddleRule( _, Ant( 0 ), _, il ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, Some( aux1 ) )

        val tr = translate(
          rightSubProof,
          if ( rightSubProof.endSequent.succedent.nonEmpty )
            Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) )
          else None )

        val i = tr.endSequent.indexOf( rightSubProof.endSequent( aux2 ), Polarity.InAntecedent )

        val partialProof = ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          qed
        exchange( partialProof, focus.map( p.endSequent.apply ) )

      // Propositional rules
      case p @ NegLeftRule( subProof, aux ) =>
        focus.map( p.endSequent.apply ) match {
          case Some( f ) =>
            val focusMain = subProof.endSequent.indexOf( f, Polarity.InSuccedent )
            translate( subProof, Some( focusMain ) )
          case None =>
            val Neg( a ) = p.mainFormula
            val focusMain = subProof.endSequent.indexOf( a, Polarity.InSuccedent )
            ProofBuilder.
              c( nd.LogicalAxiom( p.mainFormula ) ).
              c( translate( subProof, Some( focusMain ) ) ).
              b( NegElimRule( _, _ ) ).
              qed
        }

      case p @ NegRightRule( subProof, aux ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Neg( a ) = p.mainFormula
          val t = translate( subProof, heuristicIndex( subProof ) )
          if ( t.endSequent( Suc( 0 ) ) == Bottom() ) {
            NegIntroRule( t, a )
          } else {
            ProofBuilder.
              c( nd.LogicalAxiom( -t.endSequent( Suc( 0 ) ) ) ).
              c( t ).
              b( NegElimRule( _, _ ) ).
              u( NegIntroRule( _, a ) ).
              qed
          }
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case p @ AndLeftRule( subProof, aux1, aux2 ) =>

        val t = translate(
          subProof,
          if ( p.endSequent.succedent.nonEmpty )
            Some( p.getSequentConnector.parent( focus.get ) )
          else None )

        val And( a, b ) = p.mainFormula

        val ax = nd.LogicalAxiom( p.mainFormula )
        ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, a ) ).
          c( ax ).
          u( AndElim1Rule( _ ) ).
          b( ImpElimRule( _, _ ) ).
          u( ImpIntroRule( _, b ) ).
          c( ax ).
          u( AndElim2Rule( _ ) ).
          b( ImpElimRule( _, _ ) ).
          u( ContractionRule( _, p.mainFormula ) ).
          qed

      case p @ AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val tl = translate( leftSubProof, Some( aux1 ) )
          val tr = translate( rightSubProof, Some( aux2 ) )

          AndIntroRule( tl, tr )
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate(
          leftSubProof,
          if ( leftSubProof.endSequent.succedent.nonEmpty )
            Some( p.getLeftSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) )
          else None )
        val wtl = if ( p.endSequent.succedent.nonEmpty &&
          p.getLeftSequentConnector.parentOption( focus.get ) == None ) {
          if ( tl.endSequent( Suc( 0 ) ) == Bottom() )
            BottomElimRule( tl, p.endSequent( focus.get ) )
          else {
            ProofBuilder.
              c( nd.LogicalAxiom( -tl.endSequent( Suc( 0 ) ) ) ).
              c( tl ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, p.endSequent( focus.get ) ) ).
              qed
          }
        } else tl

        val tr = translate(
          rightSubProof,
          if ( rightSubProof.endSequent.succedent.nonEmpty )
            Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) )
          else None )
        val wtr = if ( p.endSequent.succedent.nonEmpty &&
          p.getRightSequentConnector.parentOption( focus.get ) == None ) {
          if ( tr.endSequent( Suc( 0 ) ) == Bottom() )
            BottomElimRule( tr, p.endSequent( focus.get ) )
          else {
            ProofBuilder.
              c( nd.LogicalAxiom( -tr.endSequent( Suc( 0 ) ) ) ).
              c( tr ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, p.endSequent( focus.get ) ) ).
              qed
          }
        } else tr

        OrElimRule( nd.LogicalAxiom( p.mainFormula ), wtl, wtr )

      case p @ OrRightRule(
        subProof1 @ WeakeningRightRule( subProof2, f ), aux1, aux2
        ) if f == subProof1.endSequent( aux1 ) || f == subProof1.endSequent( aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Or( a, b ) = p.mainFormula
          f match {
            case `b` =>
              val i = subProof1.getSequentConnector.parent( aux1 )
              ProofBuilder.
                c( translate( subProof2, Some( i ) ) ).
                u( OrIntro1Rule( _, f ) ).
                qed
            case `a` =>
              val i = subProof1.getSequentConnector.parent( aux2 )
              ProofBuilder.
                c( translate( subProof2, Some( i ) ) ).
                u( OrIntro2Rule( _, f ) ).
                qed
          }
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case p @ OrRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Or( a, b ) = p.mainFormula
          val rp = ProofBuilder.
            c( translate( subProof, Some( aux2 ) ) ).
            u( OrIntro2Rule( _, a ) ).
            qed

          val lp = ProofBuilder.
            c( nd.LogicalAxiom( a ) ).
            u( OrIntro1Rule( _, b ) ).
            qed

          val i = rp.endSequent.indexOf( Neg( a ), Polarity.InAntecedent )
          ExcludedMiddleRule( lp, Ant( 0 ), rp, i )
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

        val tl = translate( leftSubProof, Some( aux1 ) )

        val tr = translate(
          rightSubProof,
          if ( rightSubProof.endSequent.succedent.nonEmpty )
            Some( p.getRightSequentConnector.parentOption( focus.get ).getOrElse( Suc( 0 ) ) )
          else None )

        val Imp( _, b ) = p.mainFormula
        val i = tr.endSequent.indexOf( b, Polarity.InAntecedent )

        val partialProof = ProofBuilder.
          c( tr ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( tl ).
          b( ImpElimRule( _, _ ) ).
          b( ImpElimRule( _, _ ) ).
          qed

        exchange( partialProof, focus.map( p.endSequent.apply ) )

      case p @ ImpRightRule( subProof, aux1, aux2 ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Imp( a, _ ) = p.mainFormula
          ProofBuilder.
            c( translate( subProof, Some( aux2 ) ) ).
            u( ImpIntroRule( _, a ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      // Quantifier rules
      case p @ ForallLeftRule( subProof, aux, a: Formula, term: Expr, v: Var ) =>

        val t = translate(
          subProof,
          if ( p.endSequent.succedent.nonEmpty )
            Some( p.getSequentConnector.parent( focus.get ) )
          else None )

        val i = t.endSequent.indexOf( Substitution( v, term )( a ), Polarity.InAntecedent )
        ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, i ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          u( ForallElimRule( _, term ) ).
          b( ImpElimRule( _, _ ) ).
          qed

      case p @ ForallRightRule( subProof, aux, eigen, _ ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          ProofBuilder.
            c( translate( subProof, Some( aux ) ) ).
            u( ForallIntroRule( _, p.mainFormula, eigen ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case ForallSkRightRule( subProof, aux, main, skT ) =>
        throw new LKToNDTranslationException(
          "ForallSkRightRule",
          "LK proofs containing skolem functions are not supported." )

      case p @ ExistsLeftRule( subProof, aux, eigen, v ) =>

        val t = translate(
          subProof,
          if ( p.endSequent.succedent.nonEmpty )
            Some( p.getSequentConnector.parent( focus.get ) )
          else None )

        val Ex( _, a ) = p.mainFormula
        val i = t.endSequent.indexOf( Substitution( v, eigen )( a ), Polarity.InAntecedent )
        ProofBuilder.
          c( nd.LogicalAxiom( p.mainFormula ) ).
          c( t ).
          b( ExistsElimRule( _, _, i, eigen ) ).
          qed

      case ExistsSkLeftRule( subProof, aux, main, skT ) =>
        throw new LKToNDTranslationException(
          "ExistsSkLeftRule",
          "LK proofs containing skolem functions are not supported." )

      case p @ ExistsRightRule( subProof, aux, _, t, _ ) =>

        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          ProofBuilder.
            c( translate( subProof, Some( aux ) ) ).
            u( ExistsIntroRule( _, p.mainFormula, t ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      // Equality rules
      case p @ EqualityLeftRule( subProof, eq, aux, replacementContext ) =>

        val t = translate(
          subProof,
          if ( p.endSequent.succedent.nonEmpty )
            Some( p.getSequentConnector.parent( focus.get ) )
          else None )

        val Abs( x, term ) = replacementContext

        ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, subProof.endSequent( aux ) ) ).
          c( nd.LogicalAxiom( subProof.endSequent( eq ) ) ).
          c( nd.LogicalAxiom( p.mainFormula ) ).
          b( EqualityElimRule( _, _, term.asInstanceOf[Formula], x ) ).
          b( ImpElimRule( _, _ ) ).
          u( ContractionRule( _, subProof.endSequent( eq ) ) ).
          qed

      case p @ EqualityRightRule( subProof, eq, aux, replacementContext ) =>
        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val Abs( x, term ) = replacementContext

          ProofBuilder.
            c( nd.LogicalAxiom( subProof.endSequent( eq ) ) ).
            c( translate( subProof, Some( aux ) ) ).
            b( EqualityElimRule( _, _, term.asInstanceOf[Formula], x ) ).
            u( ContractionRule( _, subProof.endSequent( eq ) ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }

      case lk.rules.InductionRule( cases, formula, term ) =>
        val ndCases = cases.map {
          case lk.rules.InductionCase( proof, constructor, hypotheses, eigenVars, conclusion ) =>
            val prfNd = translate( proof, Some( conclusion ) )
            val hypNd = hypotheses.map { case i: SequentIndex => prfNd.endSequent.indexOf( proof.endSequent( i ) ) }
            nd.InductionCase( prfNd, constructor, hypNd, eigenVars )
        }
        nd.InductionRule( ndCases, formula, term )

      case p @ ConversionLeftRule( subProof: LKProof, aux: SequentIndex, main: Formula ) =>
        val t = translate( subProof, focus )
        ProofBuilder.
          c( t ).
          u( ImpIntroRule( _, subProof.endSequent( aux ) ) ).
          u( nd.DefinitionRule( _, Imp( main, t.endSequent( Suc( 0 ) ) ) ) ).
          c( nd.LogicalAxiom( main ) ).
          b( ImpElimRule( _, _ ) ).
          qed

      case p @ ConversionRightRule( subProof, aux, main ) =>
        if ( p.mainFormula == p.endSequent( focus.get ) ) {
          val t = translate( subProof, focus )
          ProofBuilder.
            c( t ).
            u( nd.DefinitionRule( _, main ) ).
            qed
        } else {
          val focusMain = p.endSequent.indexOf( p.mainFormula, Polarity.InSuccedent )
          exchange( translate( proof, Some( focusMain ) ), focus.map( p.endSequent.apply ) )
        }
    }
    check( ndProof, proof, focus )
    ndProof
  }
}

class LKToNDTranslationException( name: String, message: String )
  extends Exception( s"Cannot translate $name: " + message )
