package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.Definitions
import at.logic.gapt.proofs.{ Ant, Context, SequentConnector, Suc }

/**
 * Eliminates definitions from a lambda expression, HOL formula, or LK proof.
 */
object eliminateDefinitions {
  /**
   * Creates a new `eliminateDefinitions` object.
   * @param dmap The definitions to be eliminated.
   */
  def apply( dmap: Map[_ <: Const, _ <: Expr] ): eliminateDefinitions =
    new eliminateDefinitions( Normalizer( dmap.map( ReductionRule.apply ) ) )

  /**
   * Given an implicit [[at.logic.gapt.proofs.Context]] in scope, this removes all definitions in that context from a
   * proof.
   * @param proof The proof to be transformed.
   * @param ctx An implicit context. Definitions in this will be removed from proof.
   */
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    apply( proof, ctx.normalizer )

  def apply( proof: LKProof, normalizer: Normalizer ): LKProof =
    new eliminateDefinitions( normalizer ).apply( proof )
}

/**
 * Implements definition elimination.
 */
class eliminateDefinitions private ( normalizer: Normalizer ) extends Function[Expr, Expr] {
  def apply( e: Expr ): Expr = normalizer.normalize( e )
  def apply( f: Formula ): Formula = apply( f: Expr ).asInstanceOf[Formula]

  def apply( proof: LKProof ): LKProof = proof match {
    // introductory rules
    case LogicalAxiom( atom )     => LogicalAxiom( apply( atom ) )

    case TopAxiom                 => TopAxiom
    case BottomAxiom              => BottomAxiom

    case ReflexivityAxiom( term ) => ReflexivityAxiom( apply( term ) )

    case ProofLink( name, seq )   => ProofLink( apply( name ), seq map apply )

    //structural rules
    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      CutRule( apply( leftSubProof ), aux1, apply( rightSubProof ), aux2 )

    case WeakeningLeftRule( subProof, main ) =>
      WeakeningLeftRule( apply( subProof ), apply( main ) )

    case WeakeningRightRule( subProof, main ) =>
      WeakeningRightRule( apply( subProof ), apply( main ) )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      ContractionLeftRule( apply( subProof ), aux1, aux2 )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      ContractionRightRule( apply( subProof ), aux1, aux2 )

    //logical rules
    case NegLeftRule( subProof, aux ) =>
      NegLeftRule( apply( subProof ), aux )

    case NegRightRule( subProof, aux ) =>
      NegRightRule( apply( subProof ), aux )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      AndLeftRule( apply( subProof ), aux1, aux2 )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      AndRightRule( apply( leftSubProof ), aux1, apply( rightSubProof ), aux2 )

    case OrRightRule( subProof, aux1, aux2 ) =>
      OrRightRule( apply( subProof ), aux1, aux2 )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      OrLeftRule( apply( leftSubProof ), aux1, apply( rightSubProof ), aux2 )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ImpLeftRule( apply( leftSubProof ), aux1, apply( rightSubProof ), aux2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      ImpRightRule( apply( subProof ), aux1, aux2 )

    //quantfication rules
    case ForallLeftRule( subProof, aux, f, term, quant ) =>
      ForallLeftRule( apply( subProof ), aux, apply( f ), apply( term ), quant )

    case ExistsRightRule( subProof, aux, f, term, quant ) =>
      ExistsRightRule( apply( subProof ), aux, apply( f ), apply( term ), quant )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      ExistsLeftRule( apply( subProof ), aux, eigen, quant )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      ForallRightRule( apply( subProof ), aux, eigen, quant )

    case ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
      ExistsSkLeftRule( apply( subProof ), aux, apply( main ), apply( skT ), apply( skD ) )

    case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
      ForallSkRightRule( apply( subProof ), aux, apply( main ), apply( skT ), apply( skD ) )

    //equational rules
    case proof @ EqualityLeftRule( subProof, eq, aux, con ) =>
      EqualityLeftRule( apply( subProof ), eq, aux, apply( con ).asInstanceOf[Abs] )

    case proof @ EqualityRightRule( subProof, eq, aux, con ) =>
      EqualityRightRule( apply( subProof ), eq, aux, apply( con ).asInstanceOf[Abs] )

    /* The cases for definition rules employ a trick: The removal of the rule would change the order of the end
        sequent. We use exchange macro rules to artificially replicate the movement of formulas that the definition
         rule would have performed.*/

    case proof @ DefinitionLeftRule( subProof, aux, _ ) =>
      if ( apply( proof.auxFormula ) == apply( proof.mainFormula ) )
        ExchangeLeftMacroRule( apply( subProof ), aux )
      else
        DefinitionLeftRule( apply( subProof ), aux, apply( proof.mainFormula ) )

    case proof @ DefinitionRightRule( subProof, aux, _ ) =>
      if ( apply( proof.auxFormula ) == apply( proof.mainFormula ) )
        ExchangeRightMacroRule( apply( subProof ), aux )
      else
        DefinitionRightRule( apply( subProof ), aux, apply( proof.mainFormula ) )

    case InductionRule( cases, main, term ) =>
      InductionRule( cases map { cs => cs.copy( proof = apply( cs.proof ) ) }, apply( main ).asInstanceOf[Abs], apply( term ) )
  }
}
