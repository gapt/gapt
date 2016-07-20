package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent

import scala.collection.mutable

/**
 * Eliminate [[AvatarSplit]], [[AvatarComponent]], [[AvatarContradiction]]
 * splitting inferences from a resolution proof.
 */
object eliminateSplitting {

  def apply( p: ResolutionProof ): ResolutionProof = {
    if ( !p.subProofs.exists { _.isInstanceOf[AvatarContradiction] } ) return p
    nonGroundSplits( groundSplits( p ) )
  }

  /**
   * Eliminates splitting inferences on ground literals by replacing them with [[Taut]].
   */
  private def groundSplits( p: ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()
    def factor( p: ResolutionProof, q: ResolutionProof ) = Factor( q, p.conclusion ++ p.assertions diff q.assertions )
    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, factor( p, p match {
      case Resolution( p1, i1, p2, i2 ) =>
        Resolution( f( p1 ), f( p2 ), p1.conclusion( i1 ) )
      case p @ Factor( p1, i1, i2 ) =>
        val q1 = f( p1 )
        val Seq( j1, j2 ) = q1.conclusion.indicesWherePol( _ == p1.conclusion( i1 ), i1.isSuc ).take( 2 )
        Factor( q1, j1, j2 )
      case p @ Paramod( p1, i1, ltr, p2, i2, ctx ) =>
        val q1 = f( p1 )
        val q2 = f( p2 )
        Paramod( q1, q1.conclusion.indexOfInSuc( p1.conclusion( i1 ) ), ltr,
          q2, q2.conclusion.indexOfPol( p2.conclusion( i2 ), i2.isSuc ), ctx )
      case p @ Flip( p1, i1 ) =>
        val q1 = f( p1 )
        Flip( q1, q1.conclusion.indexOfPol( p1.conclusion( i1 ), i1.isSuc ) )
      case Subst( p1, subst ) => Subst( f( p1 ), subst )
      case AvatarContradiction( p1 ) =>
        val q1 = f( p1 )
        if ( q1.assertions.isEmpty ) q1 else AvatarContradiction( q1 )
      case AvatarComponent( AvatarGroundComp( atom, _ ) )       => Taut( atom )
      case AvatarSplit( p1, indices, AvatarGroundComp( _, _ ) ) => f( p1 )
      case AvatarSplit( p1, indices, comp ) =>
        AvatarSplit( f( p1 ), comp )
      case _ => p
    } ) )
    f( p )
  }

  /**
   * Given a non-ground splitting component C with atom A and a proof that ends with A in the assertion,
   * eliminate [[AvatarSplit]] inferences that move C into the assertion,
   * and return a proof that ends with C in the conclusion.
   */
  private def project( p: ResolutionProof, splAtom: HOLAtom ): ( ResolutionProof, Seq[Var], HOLSequent ) = {
    val ngc = p.subProofs.collect { case AvatarSplit( _, _, comp @ AvatarNonGroundComp( `splAtom`, _, _ ) ) => comp }.head
    val newVs = ngc.vars map rename( ngc.vars, freeVariables( p.subProofs.flatMap( _.conclusion.elements ) ) )
    val newClause = Substitution( ngc.vars zip newVs )( ngc.clause )

    val memo = mutable.Map[ResolutionProof, ResolutionProof]()
    def factor( p: ResolutionProof, q: ResolutionProof ) =
      Factor(
        q,
        if ( p.assertions.succedent contains splAtom )
          p.conclusion ++ newClause
        else
          p.conclusion
      )
    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, factor( p, p match {
      case _ if !p.assertions.succedent.contains( splAtom ) => p
      case Resolution( p1, i1, p2, i2 ) =>
        Resolution( f( p1 ), f( p2 ), p1.conclusion( i1 ) )
      case p @ Factor( p1, i1, i2 ) =>
        val q1 = f( p1 )
        val Seq( j1, j2 ) = q1.conclusion.indicesWherePol( _ == p1.conclusion( i1 ), i1.isSuc ).take( 2 )
        Factor( q1, j1, j2 )
      case p @ Paramod( p1, i1, ltr, p2, i2, ctx ) =>
        val q1 = f( p1 )
        val q2 = f( p2 )
        Paramod( q1, q1.conclusion.indexOfInSuc( p1.conclusion( i1 ) ), ltr,
          q2, q2.conclusion.indexOfPol( p2.conclusion( i2 ), i2.isSuc ), ctx )
      case p @ Flip( p1, i1 ) =>
        val q1 = f( p1 )
        Flip( q1, q1.conclusion.indexOfPol( p1.conclusion( i1 ), i1.isSuc ) )
      case Subst( p1, subst ) => Subst( f( p1 ), subst )
      case AvatarSplit( p1, indices, AvatarNonGroundComp( `splAtom`, _, vs ) ) =>
        Subst( f( p1 ), Substitution( vs zip newVs ) )
      case AvatarSplit( p1, indices, comp ) =>
        AvatarSplit( f( p1 ), comp )
      case _ => p
    } ) )

    ( f( p ), newVs, newClause )
  }

  /**
   * Given a non-ground splitting component C with atom A as well as a projection that ends with C in the conclusion,
   * replace all [[AvatarComponent]] inferences for that component with the projection.
   */
  private def replace( p: ResolutionProof, splAtom: HOLAtom, proj: ResolutionProof, projVars: Seq[Var], projClause: HOLSequent ): ResolutionProof = {
    val extraAssumptions = proj.conclusion diff projClause
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()
    def factor( p: ResolutionProof, q: ResolutionProof ) =
      Factor(
        q,
        if ( p.assertions.antecedent.contains( splAtom ) )
          p.conclusion ++ extraAssumptions
        else
          p.conclusion
      )
    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, factor( p, p match {
      case _ if !p.assertions.antecedent.contains( splAtom ) => p
      case Resolution( p1, i1, p2, i2 ) =>
        Resolution( f( p1 ), f( p2 ), p1.conclusion( i1 ) )
      case p @ Factor( p1, i1, i2 ) =>
        val q1 = f( p1 )
        val Seq( j1, j2 ) = q1.conclusion.indicesWherePol( _ == p1.conclusion( i1 ), i1.isSuc ).take( 2 )
        Factor( q1, j1, j2 )
      case p @ Paramod( p1, i1, ltr, p2, i2, ctx ) =>
        val q1 = f( p1 )
        val q2 = f( p2 )
        Paramod( q1, q1.conclusion.indexOfInSuc( p1.conclusion( i1 ) ), ltr,
          q2, q2.conclusion.indexOfPol( p2.conclusion( i2 ), i2.isSuc ), ctx )
      case p @ Flip( p1, i1 ) =>
        val q1 = f( p1 )
        Flip( q1, q1.conclusion.indexOfPol( p1.conclusion( i1 ), i1.isSuc ) )
      case Subst( p1, subst ) => Subst( f( p1 ), subst )
      case AvatarComponent( AvatarNonGroundComp( `splAtom`, _, vs ) ) =>
        Subst( proj, Substitution( projVars zip vs ) )
      case AvatarSplit( p1, indices, comp ) =>
        AvatarSplit( f( p1 ), comp )
      case _ => p
    } ) )
    f( p )
  }

  /**
   * Eliminate non-ground splitting inferences.  This procedure is similar to Π_1-normalization in natural deduction.
   * As a strategy, we pick a top-most resolution inference on a splitting atom (i.e. one that is
   * right below [[AvatarContradiction]] inferences), call [[project]] on the left sub-proof,
   * and then put the projection in the right sub-proof with [[replace]].
   */
  private def nonGroundSplits( p: ResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()
    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case AvatarContradiction( p1 ) => AvatarContradiction( Factor( p1 ) )
      case Resolution( p1, i1, p2, i2 ) =>
        val splAtom = p1.conclusion( i1 ).asInstanceOf[HOLAtom]
        ( f( p1 ), f( p2 ) ) match {
          case ( Factor.Block( AvatarContradiction( q1 ) ), Factor.Block( AvatarContradiction( q2 ) ) ) =>
            if ( q1.assertions.succedent.contains( splAtom ) ) {
              val ( proj, projVars, projClause ) = project( q1, splAtom )
              val repld = replace( q2, splAtom, proj, projVars, projClause )
              Factor( if ( repld.assertions.nonEmpty ) AvatarContradiction( repld ) else repld )
            } else {
              AvatarContradiction( Factor( Resolution.maybe( Factor( q1 ), Factor( q2 ), splAtom ) ) )
            }
          case ( Factor.Block( AvatarContradiction( q1 ) ), q2 ) =>
            AvatarContradiction( Factor( Resolution.maybe( Factor( q1 ), q2, splAtom ) ) )
          case ( q1, Factor.Block( AvatarContradiction( q2 ) ) ) =>
            AvatarContradiction( Factor( Resolution.maybe( q1, Factor( q2 ), splAtom ) ) )
          case ( q1, q2 ) =>
            Factor( Resolution.maybe( q1, q2, splAtom ) )
        }
      case Factor( p1, i1, i2 ) => f( p1 )
      case _ =>
        require( !p.subProofs.exists { _.isInstanceOf[AvatarContradiction] } )
        p
    } )

    f( p ) match {
      case AvatarContradiction( q ) => q
      case q                        => q
    }
  }

}
