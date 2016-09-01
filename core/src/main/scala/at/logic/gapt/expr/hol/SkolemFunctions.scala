package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.epsilon.Epsilon
import at.logic.gapt.utils.linearizeStrictPartialOrder

/**
 * List of definitions of Skolem symbols.
 *
 * A Skolem definition is similar but slightly different from the epsilon operator:
 *
 * Syntactically it is a map s_i → λx_1 .. λx_n Qy φ(x_1, .., x_n, y), where Q is a quantifier.
 * Then s_i(x_1, .., x_n) is the Skolem term used for the formula Qy φ(x_1, .., x_n, y), where Qy is strong.
 *
 * This Skolem term corresponds to the epsilon term εy φ(x_1, .., x_n, y) or εy ¬φ(x_1, .., x_n),
 * depending on whether Q is ∃ or ∀.  The reason we don't use epsilon terms directly is that this makes
 * it impossible to deskolemize a formula based on just the Skolem definitions:
 * for example both ∃x ∀y φ and ∃x ¬∃y¬ φ would define their Skolem functions using the same epsilon terms.
 */
case class SkolemFunctions( skolemDefs: Map[Const, LambdaExpression] ) {
  skolemDefs foreach {
    case ( s, d @ Abs.Block( vs, Quant( v, f ) ) ) =>
      require( s.exptype == FunctionType( v.exptype, vs map { _.exptype } ) )
      require( freeVariables( d ).isEmpty )
  }

  val Right( dependencyOrder ) = linearizeStrictPartialOrder(
    skolemDefs.keySet,
    for ( ( s, d ) <- skolemDefs; s_ <- constants( d ) if skolemDefs contains s_ ) yield s -> s_
  )

  def orderedDefinitions = dependencyOrder.map( c => c -> skolemDefs( c ) )

  def epsilonDefinitions =
    for ( ( skConst, skDef ) <- orderedDefinitions )
      yield skConst -> ( skolemDefs( skConst ) match {
      case Abs.Block( vs, Ex( v, f ) )  => Abs.Block( vs, Epsilon( v, f ) )
      case Abs.Block( vs, All( v, f ) ) => Abs.Block( vs, Epsilon( v, -f ) )
    } )

  override def toString =
    ( for ( ( s, d ) <- orderedDefinitions ) yield s"$s → $d\n" ).mkString
}
object SkolemFunctions {
  def apply( skolemDefs: Iterable[( Const, LambdaExpression )] ): SkolemFunctions =
    SkolemFunctions( skolemDefs groupBy { _._1 } map {
      case ( c, ds ) =>
        require(
          ds.size == 1,
          s"Inconsistent skolem symbol $c:\n${ds.map { _._2 }.mkString( "\n" )}"
        )
        c -> ds.head._2
    } )
}
