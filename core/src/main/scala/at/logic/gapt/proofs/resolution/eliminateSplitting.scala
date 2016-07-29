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
  private def groundSplits( p: ResolutionProof ): ResolutionProof =
    new ResolutionProofVisitor {
      override def visitAvatarComponent( p: AvatarComponent ): ResolutionProof =
        p.component match {
          case AvatarGroundComp( atom, _ ) => Taut( atom )
          case _                           => p
        }

      override def visitAvatarSplit( p: AvatarSplit ): ResolutionProof =
        p.component match {
          case AvatarGroundComp( atom, _ ) => recurse( p.subProof )
          case _                           => super.visitAvatarSplit( p )
        }
    }.apply( p )

  /**
   * Given a non-ground splitting component C with atom A and a proof that ends with A in the assertion,
   * eliminate [[AvatarSplit]] inferences that move C into the assertion,
   * and return a proof that ends with C in the conclusion.
   */
  private def project( p: ResolutionProof, splAtom: HOLAtom ): ( ResolutionProof, Seq[Var], HOLSequent ) = {
    val ngc = p.subProofs.collect { case AvatarSplit( _, _, comp @ AvatarNonGroundComp( `splAtom`, _, _ ) ) => comp }.head
    val newVs = ngc.vars map rename( ngc.vars, containedNames( p ) )
    val newClause = Substitution( ngc.vars zip newVs )( ngc.clause )

    val visitor = new ResolutionProofVisitor {
      override def visitAvatarSplit( p: AvatarSplit ): ResolutionProof =
        p.component match {
          case AvatarNonGroundComp( `splAtom`, _, vs ) =>
            Subst( recurse( p.subProof ), Substitution( vs zip newVs ) )
          case _ => super.visitAvatarSplit( p )
        }
    }

    ( visitor( p ), newVs, newClause )
  }

  /**
   * Given a non-ground splitting component C with atom A as well as a projection that ends with C in the conclusion,
   * replace all [[AvatarComponent]] inferences for that component with the projection.
   */
  private def replace( p: ResolutionProof, splAtom: HOLAtom, proj: ResolutionProof, projVars: Seq[Var] ) =
    new ResolutionProofVisitor {
      override def visitAvatarComponent( p: AvatarComponent ): ResolutionProof =
        p.component match {
          case AvatarNonGroundComp( `splAtom`, _, vs ) =>
            Subst( proj, Substitution( projVars zip vs ) )
          case _ => p
        }
    }.apply( p )

  /**
   * Eliminate non-ground splitting inferences.  This procedure is similar to Π_1-normalization in natural deduction.
   * As a strategy, we pick a top-most resolution inference on a splitting atom (i.e. one that is
   * right below [[AvatarContradiction]] inferences), call [[project]] on the left sub-proof,
   * and then put the projection in the right sub-proof with [[replace]].
   */
  // TODO: SMT splitting
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
              val repld = replace( q2, splAtom, proj, projVars )
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
