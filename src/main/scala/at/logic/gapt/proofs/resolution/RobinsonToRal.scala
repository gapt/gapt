package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.ral._

object RobinsonToRal extends RobinsonToRal {
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

  /* convert subsitution will be called on any substitution before translation */
  def convert_substitution( s: Substitution ): Substitution;

  def apply( p: ResolutionProof ): RalProof = p match {
    case _: InitialClause             => RalInitial( p.conclusion map convert_formula map { Seq[LambdaExpression]() -> _ } )
    case Factor( p1, i1, i2 )         => RalFactor( apply( p1 ), i1, i2 )
    case Instance( p1, subst )        => RalSub( apply( p1 ), convert_substitution( subst ) )
    case Resolution( p1, i1, p2, i2 ) => RalCut( apply( p1 ), Seq( i1 ), apply( p2 ), Seq( i2 ) )
    case Paramodulation( p1, eq, p2, lit, pos, dir ) =>
      eq match {
        case Ant( _ ) =>
          throw new Exception( "Sequent index of equality in para rule must be in succedent!" )
        case seq @ Suc( _ ) =>
          RalPara( apply( p1 ), seq, apply( p2 ), lit, pos, dir )
      }

  }
}
