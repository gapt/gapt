package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.ral._

object RobinsonToRal extends RobinsonToRal {
  /* One of our heuristics maps higher-order types into first-order ones. When the proof is converted to Ral,
   * convert_formula and convert_substitution map the types back, if possible. The reason it is part of the
   * Ral transformation is that before the layer cleanup we also needed to convert all formulas to the same layer type
   * (i.e. not mix FOLFormulas with HOLFormulas).
   */
  @deprecated( "No idea what this should do", "2015-05-03" )
  override def convert_formula( e: HOLFormula ): HOLFormula = e
  @deprecated( "No idea what this should do", "2015-05-03" )
  override def convert_substitution( s: Substitution ): Substitution = s

  //TODO: this is somehow dirty....
  def convert_map( m: Map[Var, LambdaExpression] ): Substitution =
    Substitution( m.asInstanceOf[Map[Var, LambdaExpression]] )
}

abstract class RobinsonToRal {
  /* convert formula will be called on any formula before translation */
  def convert_formula( e: HOLFormula ): HOLFormula;

  /* convert substitution will be called on any substitution before translation */
  def convert_substitution( s: Substitution ): Substitution;

  def apply( p: ResolutionProof ): RalProof = p match {
    case _: InitialClause             => RalInitial( p.conclusion map convert_formula map { Seq[LambdaExpression]() -> _ } )
    case Factor( p1, i1, i2 )         => RalFactor( apply( p1 ), i1, i2 )
    case Instance( p1, subst )        => RalSub( apply( p1 ), convert_substitution( subst ) )
    case Resolution( p1, i1, p2, i2 ) => RalCut( apply( p1 ), Seq( i1 ), apply( p2 ), Seq( i2 ) )
    case Paramodulation( p1, eq @ Suc( _ ), p2, lit, pos, dir ) =>
      RalPara( apply( p1 ), eq, apply( p2 ), lit, pos, dir )
  }
}
