package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.undoHol2Fol.Signature
import at.logic.gapt.expr.fol.{ undoHol2Fol, replaceAbstractions }
import at.logic.gapt.proofs.{ Suc, Ant }
import at.logic.gapt.proofs.ral._

object RobinsonToRal extends RobinsonToRal {
  /* One of our heuristics maps higher-order types into first-order ones. When the proof is converted to Ral,
   * convert_formula and convert_substitution map the types back, if possible. The reason it is part of the
   * Ral transformation is that before the layer cleanup we also needed to convert all formulas to the same layer type
   * (i.e. not mix FOLFormulas with HOLFormulas).
   */
  override def convert_formula( e: HOLFormula ): HOLFormula = e
  override def convert_substitution( s: Substitution ): Substitution = s

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

/**
 * A converter from Robinson resolution proofs to Ral proofs, which reintroduces the lambda abstractions
 * which we removed for the fol export.
 *
 * @param sig_vars The signature of the variables in the original proof
 * @param sig_consts The signature of constants in the original proof
 * @param cmap The mapping of abstracted symbols to lambda terms. The abstracted symbols must be unique (i.e. cmap
 *             must be a bijection)
 */
class Robinson2RalWithAbstractions(
    sig_vars:   Map[String, List[Var]],
    sig_consts: Map[String, List[Const]],
    cmap:       replaceAbstractions.ConstantsMap
) extends RobinsonToRal {
  //we know that the cmap is a bijection and define absmap as the inverse of cmap
  val absmap = Map[String, LambdaExpression]() ++ ( cmap.toList.map( x => ( x._2.toString, x._1 ) ) )

  private def bt( e: LambdaExpression, t_expected: Option[Ty] ) = BetaReduction.betaNormalize(
    undoHol2Fol.backtranslate( e, sig_vars, sig_consts, absmap, t_expected )
  )

  override def convert_formula( e: HOLFormula ): HOLFormula = bt( e, Some( To ) ).asInstanceOf[HOLFormula]

  override def convert_substitution( s: Substitution ): Substitution = {
    val mapping = s.map.toList.map {
      case ( from, to ) =>
        ( bt( from, None ).asInstanceOf[Var], bt( to, None ) )
    }

    Substitution( mapping )
  }
}

/**
 * A converter from Robinson resolution proofs to Ral proofs, which reintroduces the lambda abstractions
 * which we removed for the fol export.
 */
object Robinson2RalWithAbstractions {

  /**
   * @param signature The signature of the original proof
   * @param cmap The mapping of abstracted symbols to lambda terms. The abstracted symbols must be unique (i.e. cmap
   *             must be a bijection)
   */
  def apply( signature: Signature, cmap: replaceAbstractions.ConstantsMap ) = {
    val ( sigc, sigv ) = signature
    new Robinson2RalWithAbstractions(
      sigv.map( x => ( x._1, x._2.toList ) ),
      sigc.map( x => ( x._1, x._2.toList ) ), cmap
    )
  }

  /**
   * @param sig_vars The signature of the variables in the original proof
   * @param sig_consts The signature of constants in the original proof
   * @param cmap The mapping of abstracted symbols to lambda terms. The abstracted symbols must be unique (i.e. cmap
   *             must be a bijection)
   */
  def apply(
    sig_vars:   Map[String, List[Var]],
    sig_consts: Map[String, List[Const]],
    cmap:       replaceAbstractions.ConstantsMap
  ) = new Robinson2RalWithAbstractions( sig_vars, sig_consts, cmap )

}
