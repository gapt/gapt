package gapt.proofs.lk

import gapt.expr._
import BetaReduction.{ betaNormalize, _ }
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.SequentConnector
import gapt.proofs.gaptic.OpenAssumption
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
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.util.freeVariablesLK

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
  override def applySubstitution( substitution: Substitution, proof: LKProof ): LKProof =
    if ( substitution.isIdentity ) proof else {
      val sub1 = if ( substitution.typeMap.isEmpty ) substitution else {
        Substitution(
          freeVariablesLK( proof ).diff( substitution.domain ).map( v => v -> substitution( v ).asInstanceOf[Var] )
            ++ substitution.map,
          substitution.typeMap )
      }
      go( sub1, proof )
    }

  // if sub.typeMap.nonEmpty, then every free variable must in the domain of sub
  private def go( substitution: Substitution, proof: LKProof ): LKProof = proof match {
    case _ if substitution isIdentity => proof

    case ProofLink( referencedProof, linkquent ) =>
      ProofLink( betaNormalize( substitution( referencedProof ) ), linkquent.map { f => betaNormalize( substitution( f ) ) } )

    case TopAxiom              => TopAxiom
    case BottomAxiom           => BottomAxiom

    case LogicalAxiom( f )     => LogicalAxiom( betaNormalize( substitution( f ) ) )
    case ReflexivityAxiom( t ) => ReflexivityAxiom( betaNormalize( substitution( t ) ) )

    case WeakeningLeftRule( subProof, f ) =>
      val subProofNew = go( substitution, subProof )
      WeakeningLeftRule( subProofNew, betaNormalize( substitution( f ) ) )

    case WeakeningRightRule( subProof, f ) =>
      val subProofNew = go( substitution, subProof )
      WeakeningRightRule( subProofNew, betaNormalize( substitution( f ) ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = go( substitution, subProof )
      ContractionLeftRule( subProofNew, aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = go( substitution, subProof )
      ContractionRightRule( subProofNew, aux1, aux2 )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( go( substitution, leftSubProof ), go( substitution, rightSubProof ) )
      CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case NegLeftRule( subProof, aux ) =>
      val subProofNew = go( substitution, subProof )
      NegLeftRule( subProofNew, aux )

    case NegRightRule( subProof, aux ) =>
      val subProofNew = go( substitution, subProof )
      NegRightRule( subProofNew, aux )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val subProofNew = go( substitution, subProof )
      AndLeftRule( subProofNew, aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( go( substitution, leftSubProof ), go( substitution, rightSubProof ) )
      AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( go( substitution, leftSubProof ), go( substitution, rightSubProof ) )
      OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = go( substitution, subProof )
      OrRightRule( subProofNew, aux1, aux2 )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( go( substitution, leftSubProof ), go( substitution, rightSubProof ) )
      ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val subProofNew = go( substitution, subProof )
      ImpRightRule( subProofNew, aux1, aux2 )

    case p @ ForallLeftRule( subProof, aux, f, term, v ) =>
      val subProofNew = go( substitution, subProof )
      val All( newV, newF ) = substitution( p.mainFormula )
      ForallLeftRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case ForallRightRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range union freeVariables( subProof.conclusion ) )
      applySubstitution( substitution, ForallRightRule(
        applySubstitution( Substitution( eigen -> renamedEigen ), subProof ),
        aux, renamedEigen, quant ) )

    case p @ ForallRightRule( subProof, aux, eigen, quant ) =>
      val All( newQuant, _ ) = substitution( p.mainFormula )
      val newEigen = Var( eigen.name, substitution( eigen.ty ) )
      val newSubst = Substitution( substitution.map + ( eigen -> newEigen ), substitution.typeMap )
      ForallRightRule( go( newSubst, subProof ), aux, newEigen, newQuant )

    case ExistsLeftRule( subProof, aux, eigen, quant ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range union freeVariables( subProof.conclusion ) )
      applySubstitution( substitution, ExistsLeftRule(
        applySubstitution( Substitution( eigen -> renamedEigen ), subProof ),
        aux, renamedEigen, quant ) )

    case p @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val Ex( newQuant, _ ) = substitution( p.mainFormula )
      val newEigen = Var( eigen.name, substitution( eigen.ty ) )
      val newSubst = Substitution( substitution.map + ( eigen -> newEigen ), substitution.typeMap )
      ExistsLeftRule( go( newSubst, subProof ), aux, newEigen, newQuant )

    case p @ ExistsRightRule( subProof, aux, f, term, v ) =>
      val subProofNew = go( substitution, subProof )
      val Ex( newV, newF ) = substitution( p.mainFormula )
      ExistsRightRule( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ), newV )

    case p @ ExistsSkLeftRule( subProof, aux, main, skT ) =>
      ExistsSkLeftRule( go( substitution, subProof ), aux, BetaReduction.betaNormalize( substitution( main ) ), substitution( skT ) )

    case p @ ForallSkRightRule( subProof, aux, main, skT ) =>
      ForallSkRightRule( go( substitution, subProof ), aux, BetaReduction.betaNormalize( substitution( main ) ), substitution( skT ) )

    case EqualityLeftRule( subProof, eq, aux, con ) =>
      val subProofNew = go( substitution, subProof )
      EqualityLeftRule( subProofNew, eq, aux, substitution( con ).asInstanceOf[Abs] )

    case EqualityRightRule( subProof, eq, aux, con ) =>
      val subProofNew = go( substitution, subProof )
      EqualityRightRule( subProofNew, eq, aux, substitution( con ).asInstanceOf[Abs] )

    case InductionRule( cases, main, term ) =>
      rules.InductionRule( cases map {
        indCase( substitution, _ )
      }, substitution( main ).asInstanceOf[Abs], substitution( term ) )

    case ConversionLeftRule( subProof, aux, main ) =>
      val subProofNew = go( substitution, subProof )
      ConversionLeftRule( subProofNew, aux, substitution( main ) )

    case ConversionRightRule( subProof, aux, main ) =>
      val subProofNew = go( substitution, subProof )
      ConversionRightRule( subProofNew, aux, substitution( main ) )
  }

  private def indCase( subst: Substitution, c: InductionCase ): InductionCase =
    if ( subst.domain intersect c.eigenVars.toSet nonEmpty ) {
      indCase( Substitution( subst.map -- c.eigenVars.toSet, subst.typeMap ), c )
    } else if ( subst.range intersect c.eigenVars.toSet nonEmpty ) {
      require( !preserveEigenvariables )
      val renaming = rename( c.eigenVars, freeVariables( c.proof.endSequent ) -- c.eigenVars ++ subst.range )
      indCase( subst, c.copy(
        applySubstitution( Substitution( renaming ), c.proof ),
        eigenVars = c.eigenVars map renaming ) )
    } else {
      val newEigens = subst( c.eigenVars ).map( _.asInstanceOf[Var] )
      c.copy(
        go( Substitution( subst.map ++ ( c.eigenVars zip newEigens ), subst.typeMap ), c.proof ),
        constructor = subst( c.constructor ).asInstanceOf[Const],
        eigenVars = newEigens )
    }
}

class LKProofReplacer( repl: PartialFunction[Expr, Expr] ) {

  def apply( proof: LKProof ): LKProof = lkProofReplacerVisitor( proof, () )

  private object lkProofReplacerVisitor extends LKVisitor[Unit] {

    override protected def visitOpenAssumption( proof: OpenAssumption, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val proofNew = OpenAssumption( for ( ( l, f ) <- proof.labelledSequent ) yield l -> TermReplacement( f, repl ), proof.index )
      ( proofNew, SequentConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map {
        Seq( _ )
      } ) )
    }

    override protected def visitLogicalAxiom( proof: LogicalAxiom, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val proofNew = LogicalAxiom( TermReplacement( proof.A, repl ) )
      ( proofNew, SequentConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map {
        Seq( _ )
      } ) )
    }

    override protected def visitReflexivityAxiom( proof: ReflexivityAxiom, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val proofNew = ReflexivityAxiom( TermReplacement( proof.s, repl ) )
      ( proofNew, SequentConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map {
        Seq( _ )
      } ) )
    }

    override protected def visitProofLink( proof: ProofLink, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val proofNew = ProofLink( TermReplacement( proof.referencedProof, repl ), TermReplacement( proof.conclusion, repl ) )
      ( proofNew, SequentConnector( proofNew.conclusion, proof.conclusion, proof.conclusion.indicesSequent.map {
        Seq( _ )
      } ) )
    }

    override protected def visitWeakeningLeft( proof: WeakeningLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val ( subProofNew, subConnector ) = recurse( proof.subProof, () )
      val proofNew = WeakeningLeftRule( subProofNew, TermReplacement( proof.formula, repl ) )
      ( proofNew, ( proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) ) )
    }

    override protected def visitWeakeningRight( proof: WeakeningRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) = {
      val ( subProofNew, subConnector ) = recurse( proof.subProof, () )
      val proofNew = WeakeningRightRule( subProofNew, TermReplacement( proof.formula, repl ) )
      ( proofNew, ( proofNew.getSequentConnector * subConnector * proof.getSequentConnector.inv ) + ( proofNew.mainIndices( 0 ), proof.mainIndices( 0 ) ) )
    }

    override protected def visitForallLeft( proof: ForallLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ForallLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ), TermReplacement( proof.term, repl ) )
      }

    override protected def visitForallRight( proof: ForallRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ForallRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ),
            TermReplacement( proof.eigenVariable, repl ).asInstanceOf[Var] )
      }

    override protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ForallSkRightRule( subProofNew, subConnector.child( proof.aux ),
            TermReplacement( proof.mainFormula, repl ),
            TermReplacement( proof.skolemTerm, repl ) )
      }

    override protected def visitExistsRight( proof: ExistsRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ExistsRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ), TermReplacement( proof.term, repl ) )
      }

    override protected def visitExistsLeft( proof: ExistsLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ExistsLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ),
            TermReplacement( proof.eigenVariable, repl ).asInstanceOf[Var] )
      }

    override protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ExistsSkLeftRule( subProofNew, subConnector.child( proof.aux ),
            TermReplacement( proof.mainFormula, repl ),
            TermReplacement( proof.skolemTerm, repl ) )
      }

    override protected def visitEqualityLeft( proof: EqualityLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          EqualityLeftRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ),
            TermReplacement( proof.replacementContext, repl ).asInstanceOf[Abs] )
      }

    override protected def visitEqualityRight( proof: EqualityRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          EqualityRightRule( subProofNew, subConnector.child( proof.eq ), subConnector.child( proof.aux ),
            TermReplacement( proof.replacementContext, repl ).asInstanceOf[Abs] )
      }

    override protected def visitDefinitionLeft( proof: ConversionLeftRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ConversionLeftRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ) )
      }

    override protected def visitDefinitionRight( proof: ConversionRightRule, otherArg: Unit ): ( LKProof, SequentConnector ) =
      one2one( proof, otherArg ) {
        case Seq( ( subProofNew, subConnector ) ) =>
          ConversionRightRule( subProofNew, subConnector.child( proof.aux ), TermReplacement( proof.mainFormula, repl ) )
      }

    override protected def visitInduction( proof: InductionRule, otherArg: Unit ) =
      one2one( proof, otherArg ) { newSubProofs =>
        InductionRule(
          for ( ( ( newSubProof, subConn ), oldCase ) <- newSubProofs.zip( proof.cases ) )
            yield InductionCase( newSubProof, TermReplacement( oldCase.constructor, repl ).asInstanceOf[Const],
            oldCase.hypotheses.map( subConn.child ), oldCase.eigenVars.map( TermReplacement( _, repl ).asInstanceOf[Var] ),
            subConn.child( oldCase.conclusion ) ),
          TermReplacement( proof.formula, repl ).asInstanceOf[Abs], TermReplacement( proof.term, repl ) )
      }
  }
}