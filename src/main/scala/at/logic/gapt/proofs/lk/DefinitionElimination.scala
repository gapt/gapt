package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._

object DefinitionElimination {
  def apply( dmap: Map[LambdaExpression, LambdaExpression] ): DefinitionElimination =
    new DefinitionElimination( dmap )
}
class DefinitionElimination private ( dmap: Map[LambdaExpression, LambdaExpression] ) extends Function[LambdaExpression, LambdaExpression] {
  private val requiresMatching = dmap.keys exists { !_.isInstanceOf[Const] }

  def apply( e: LambdaExpression ): LambdaExpression = BetaReduction.betaNormalize( replace( e ) )
  def apply( f: HOLFormula ): HOLFormula = apply( f.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]

  private def replace( e: LambdaExpression ): LambdaExpression =
    replaceTopLevel( e ) map replace getOrElse ( e match {
      case App( a, b ) => App( replace( a ), replace( b ) )
      case Abs( v, t ) => Abs( v, replace( t ) )
      case _           => e
    } )

  private def replaceTopLevel( e: LambdaExpression ): Option[LambdaExpression] =
    if ( requiresMatching )
      ( for {
        ( l, r ) <- dmap.view
        subst <- syntacticMatching( l, e )
      } yield subst( r ) ) headOption
    else
      dmap get e

  def apply( proof: LKProof ): LKProof = proof match {
    // introductory rules
    case LogicalAxiom( atom )     => LogicalAxiom( apply( atom ) )

    case TopAxiom                 => TopAxiom
    case BottomAxiom              => BottomAxiom

    case ReflexivityAxiom( term ) => ReflexivityAxiom( apply( term ) )

    case TheoryAxiom( axiom )     => TheoryAxiom( axiom map apply map { _.asInstanceOf[HOLAtom] } )

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

    //equational rules
    case proof @ EqualityLeftRule( subProof, eq, aux, pos ) =>
      EqualityLeftRule( apply( subProof ), eq, aux, apply( proof.mainFormula ) )

    case proof @ EqualityRightRule( subProof, eq, aux, pos ) =>
      EqualityRightRule( apply( subProof ), eq, aux, apply( proof.mainFormula ) )

    /* The cases for definition rules employ a trick: The removal of the rule would change the order of the end
        sequent. We use exchange macro rules to artificially replicate the movement of formulas that the definition
         rule would have performed.*/

    case DefinitionLeftRule( subProof, aux, main ) =>
      ExchangeLeftMacroRule( apply( subProof ), aux )

    case DefinitionRightRule( subProof, aux, main ) =>
      ExchangeRightMacroRule( apply( subProof ), aux )

  }
}