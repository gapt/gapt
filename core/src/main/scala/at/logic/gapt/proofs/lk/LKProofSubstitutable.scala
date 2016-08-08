package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import BetaReduction._
import at.logic.gapt.proofs.OccConnector
import at.logic.gapt.proofs.gaptic.OpenAssumption

/**
 * Class that describes how LKProofs can be substituted.
 *
 * @param preserveEigenvariables  If true, preserve eigenvariables and never change them.  If false (the default),
 *                                treat eigenvariables as variables bound by their strong quantifier inferences and
 *                                perform capture-avoiding substitution.
 */
class LKProofSubstitutable( preserveEigenvariables: Boolean ) extends Substitutable[Substitution, LKProof, LKProof] {
  /**
   *
   * @param substitution The substitution to be applied.
   * @param proof The proof to apply the substitution to.
   * @return The substituted proof.
   */
  override def applySubstitution( substitution: Substitution, proof: LKProof ): LKProof = proof match {
    case _ if substitution isIdentity => proof

    case InitialSequent( sequent ) =>
      Axiom( sequent.map { f => betaNormalize( substitution( f ) ) } )

    case WeakeningLeftRule( subProof, f ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      WeakeningLeftRule( subProofNew, betaNormalize( substitution( f ) ) )

    case WeakeningRightRule( subProof, f ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      WeakeningRightRule( subProofNew, betaNormalize( substitution( f ) ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      ContractionLeftRule( subProofNew, aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      ContractionRightRule( subProofNew, aux1, aux2 )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( applySubstitution( substitution, leftSubProof ), applySubstitution( substitution, rightSubProof ) )
      CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case NegLeftRule( subProof, aux ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      NegLeftRule( subProofNew, aux )

    case NegRightRule( subProof, aux ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      NegRightRule( subProofNew, aux )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      AndLeftRule( subProofNew, aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( applySubstitution( substitution, leftSubProof ), applySubstitution( substitution, rightSubProof ) )
      AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( applySubstitution( substitution, leftSubProof ), applySubstitution( substitution, rightSubProof ) )
      OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      OrRightRule( subProofNew, aux1, aux2 )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( applySubstitution( substitution, leftSubProof ), applySubstitution( substitution, rightSubProof ) )
      ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      ImpRightRule( subProofNew, aux1, aux2 )

    case p @ ForallLeftRule( subProof, aux, f, term, v ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      val All( newV, newF ) = substitution( p.mainFormula )
      ForallLeftRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case ForallRightRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range union freeVariables( subProof.conclusion ) )
      applySubstitution( substitution, ForallRightRule(
        applySubstitution( Substitution( eigen -> renamedEigen ), subProof ),
        aux, renamedEigen, quant
      ) )

    case p @ ForallRightRule( subProof, aux, eigen, quant ) =>
      val All( newQuant, _ ) = substitution( p.mainFormula )
      ForallRightRule( applySubstitution( Substitution( substitution.map - eigen ), subProof ), aux, eigen, newQuant )

    case ExistsLeftRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range union freeVariables( subProof.conclusion ) )
      applySubstitution( substitution, ExistsLeftRule(
        applySubstitution( Substitution( eigen -> renamedEigen ), subProof ),
        aux, renamedEigen, quant
      ) )

    case p @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val Ex( newQuant, _ ) = substitution( p.mainFormula )
      ExistsLeftRule( applySubstitution( Substitution( substitution.map - eigen ), subProof ), aux, eigen, newQuant )

    case p @ ExistsRightRule( subProof, aux, f, term, v ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      val Ex( newV, newF ) = substitution( p.mainFormula )
      ExistsRightRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case p @ ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
      ExistsSkLeftRule( applySubstitution( substitution, subProof ), aux, BetaReduction.betaNormalize( substitution( main ) ), substitution( skT ), skD )

    case p @ ForallSkRightRule( subProof, aux, main, skT, skD ) =>
      ForallSkRightRule( applySubstitution( substitution, subProof ), aux, BetaReduction.betaNormalize( substitution( main ) ), substitution( skT ), skD )

    case EqualityLeftRule( subProof, eq, aux, con ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      EqualityLeftRule( subProofNew, eq, aux, substitution( con ).asInstanceOf[Abs] )

    case EqualityRightRule( subProof, eq, aux, con ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      EqualityRightRule( subProofNew, eq, aux, substitution( con ).asInstanceOf[Abs] )

    case InductionRule( cases, main, term ) =>
      InductionRule( cases map {
        indCase( substitution, _ )
      }, substitution( main ).asInstanceOf[Abs], substitution( term ) )

    case DefinitionLeftRule( subProof, aux, main ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      DefinitionLeftRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case DefinitionRightRule( subProof, aux, main ) =>
      val subProofNew = applySubstitution( substitution, subProof )
      DefinitionRightRule( subProofNew, aux, betaNormalize( substitution( main ) ) )

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }

  private def indCase( subst: Substitution, c: InductionCase ): InductionCase =
    if ( subst.domain intersect c.eigenVars.toSet nonEmpty ) {
      indCase( Substitution( subst.map -- c.eigenVars.toSet ), c )
    } else if ( subst.range intersect c.eigenVars.toSet nonEmpty ) {
      require( !preserveEigenvariables )
      val renaming = rename( c.eigenVars, freeVariables( c.proof.endSequent ) -- c.eigenVars ++ subst.range )
      indCase( subst, c.copy(
        applySubstitution( Substitution( renaming ), c.proof ),
        eigenVars = c.eigenVars map renaming
      ) )
    } else {
      c.copy( applySubstitution( subst, c.proof ) )
    }
}

class LKProofReplacer( repl: PartialFunction[LambdaExpression, LambdaExpression] ) extends LKVisitor[Unit] {
  override protected def visitOpenAssumption( proof: OpenAssumption, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val proofNew = OpenAssumption( for ( ( l, f ) <- proof.labelledSequent ) yield l -> TermReplacement( f, repl ), proof.index )
    ( proofNew, OccConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map { Seq( _ ) } ) )
  }

  override protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val proofNew = LogicalAxiom( TermReplacement( proof.A, repl ) )
    ( proofNew, OccConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map { Seq( _ ) } ) )
  }

  override protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val proofNew = ReflexivityAxiom( TermReplacement( proof.s, repl ) )
    ( proofNew, OccConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map { Seq( _ ) } ) )
  }

  override protected def visitTheoryAxiom( proof: TheoryAxiom, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val proofNew = TheoryAxiom( TermReplacement( proof.conclusion, repl ) )
    ( proofNew, OccConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map { Seq( _ ) } ) )
  }

  override protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, () )
    val proofNew = WeakeningLeftRule( subProofNew, TermReplacement( proof.formula, repl ) )
    ( proofNew, ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) ) )
  }

  override protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) = {
    val ( subProofNew, subConnector ) = recurse( proof.subProof, () )
    val proofNew = WeakeningRightRule( subProofNew, TermReplacement( proof.formula, repl ) )
    ( proofNew, ( proofNew.getOccConnector * subConnector * proof.getOccConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) ) )
  }

  override protected def visitForallLeft( proof: ForallLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ForallLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ), TermReplacement( proof.term, repl ) )
    }

  override protected def visitForallRight( proof: ForallRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ForallRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ),
          TermReplacement( proof.eigenVariable, repl ).asInstanceOf[Var] )
    }

  override protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ForallSkRightRule( subProofNew, subConnector.child( proof.aux ),
          TermReplacement( proof.mainFormula, repl ),
          TermReplacement( proof.skolemTerm, repl ),
          TermReplacement( proof.skolemDef, repl ) )
    }

  override protected def visitExistsRight( proof: ExistsRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ExistsRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ), TermReplacement( proof.term, repl ) )
    }

  override protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ExistsLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ),
          TermReplacement( proof.eigenVariable, repl ).asInstanceOf[Var] )
    }

  override protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        ExistsSkLeftRule( subProofNew, subConnector.child( proof.aux ),
          TermReplacement( proof.mainFormula, repl ),
          TermReplacement( proof.skolemTerm, repl ),
          TermReplacement( proof.skolemDef, repl ) )
    }

  override protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        EqualityLeftRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ),
          TermReplacement( proof.replacementContext, repl ).asInstanceOf[Abs] )
    }

  override protected def visitEqualityRight( proof: EqualityRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        EqualityRightRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ),
          TermReplacement( proof.replacementContext, repl ).asInstanceOf[Abs] )
    }

  override protected def visitDefinitionLeft( proof: DefinitionLeftRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        DefinitionLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.main, repl ) )
    }

  override protected def visitDefinitionRight( proof: DefinitionRightRule, otherArg: Unit ): ( LKProof, OccConnector[HOLFormula] ) =
    one2one( proof, otherArg ) {
      case Seq( ( subProofNew, subConnector ) ) =>
        DefinitionRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.main, repl ) )
    }
}