package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import BetaReduction._
import at.logic.gapt.proofs.SequentIndex
import at.logic.gapt.proofs.lkskNew.LKskProof.{ Label, LabelledFormula }

object applySubstitution {
  /**
   * Applies a substitution to an LKProof.
   *
   * @param substitution The substitution to be applied.
   * @param preserveEigenvariables  If true, preserve eigenvariables and never change them.  If false (the default),
   *                                treat eigenvariables as variables bound by their strong quantifier inferences and
   *                                perform capture-avoiding substitution.
   * @param proof The proof to apply the substitution to.
   * @return The substituted proof.
   * @note The algorithm preserves the invariant that each substituted rule works on the same sequent indices as the
   *       original rule. This is actively used in the CERES method, where the Sequent[Boolean] which characterizes
   *       the cut-ancestors is not recomputed.
   */
  def apply( substitution: Substitution, preserveEigenvariables: Boolean = false )( proof: LKskProof ): LKskProof = proof match {
    case Axiom( antlabel, suclabel, f ) =>
      Axiom( bnsub( antlabel, substitution ), bnsub( suclabel, substitution ), bnsub( f, substitution ) )

    case Reflexivity( suclabel, f ) =>
      Reflexivity( bnsub( suclabel, substitution ), bnsub( f, substitution ) )

    case WeakeningLeft( subProof, f ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      WeakeningLeft( subProofNew, bnsub( f, substitution ) )

    case WeakeningRight( subProof, f ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      WeakeningRight( subProofNew, bnsub( f, substitution ) )

    case ContractionLeft( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ContractionLeft( subProofNew, aux1, aux2 )

    case ContractionRight( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ContractionRight( subProofNew, aux1, aux2 )

    case Cut( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      Cut( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case NegLeft( subProof, aux ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      NegLeft( subProofNew, aux )

    case NegRight( subProof, aux ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      NegRight( subProofNew, aux )

    case AndLeft( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      AndLeft( subProofNew, aux1, aux2 )

    case AndRight( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      AndRight( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      OrLeft( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case OrRight( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      OrRight( subProofNew, aux1, aux2 )

    case ImpLeft( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, rightSubProofNew ) = ( apply( substitution, preserveEigenvariables )( leftSubProof ), apply( substitution, preserveEigenvariables )( rightSubProof ) )
      ImpLeft( leftSubProofNew, aux1, rightSubProofNew, aux2 )

    case ImpRight( subProof, aux1, aux2 ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      ImpRight( subProofNew, aux1, aux2 )

    //unskolemized quantifier rules
    case p @ AllLeft( subProof, aux, f, term ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val newF = substitution( p.mainFormula )
      AllLeft( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ) )

    case AllRight( subProof, aux, formula, eigen ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range.toList )
      val renamed_proof = apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof )
      apply( substitution, preserveEigenvariables )( AllRight( renamed_proof, aux, bnsub( formula, substitution ), renamedEigen ) )

    case p @ AllRight( subProof, aux, formula, eigen ) =>
      val renamed_main @ All( newQuant, _ ) = bnsub( p.mainFormula, substitution )
      val renamed_proof = apply( Substitution( substitution.map - eigen ) )( subProof )
      AllRight( renamed_proof, aux, renamed_main, newQuant )

    case ExLeft( subProof, aux, formula, eigen ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range.toList )
      val renamed_proof = apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof )
      apply( substitution, preserveEigenvariables )( ExLeft( renamed_proof, aux, bnsub( formula, substitution ), renamedEigen ) )

    case p @ ExLeft( subProof, aux, formula, eigen ) =>
      val renamed_main @ Ex( newQuant, _ ) = bnsub( p.mainFormula, substitution )
      ExLeft( apply( Substitution( substitution.map - eigen ) )( subProof ), aux, renamed_main, eigen )

    case p @ ExRight( subProof, aux, f, term ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val newF = substitution( p.mainFormula )
      ExRight( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ) )

    //skolemized quantifier rules
    case p @ AllSkLeft( subProof, aux, f, term ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val newF = substitution( p.mainFormula )
      AllSkLeft( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ) )

    case p @ AllSkRight( subProof, aux, formula, skolemconst ) =>
      val renamed_main = bnsub( p.mainFormula, substitution )
      val renamed_proof = apply( substitution )( subProof )
      AllSkRight( renamed_proof, aux, renamed_main, skolemconst )

    case p @ ExSkLeft( subProof, aux, formula, skolemconst ) =>
      val renamed_main = bnsub( p.mainFormula, substitution )
      ExSkLeft( apply( Substitution( substitution.map ) )( subProof ), aux, renamed_main, skolemconst )

    case p @ ExSkRight( subProof, aux, f, term ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      val newF = substitution( p.mainFormula )
      ExSkRight( subProofNew, aux, betaNormalize( newF ), betaNormalize( substitution( term ) ) )

    case Equality( subProof, eq, aux, flipped, pos ) =>
      val subProofNew = apply( substitution, preserveEigenvariables )( subProof )
      Equality( subProofNew, eq, aux, flipped, pos )

    case _ => throw new IllegalArgumentException( s"The rule ${proof.longName} is not handled at this time." )
  }

  def bnsub( f: LambdaExpression, sub: Substitution ): LambdaExpression = betaNormalize( sub( f ) )
  def bnsub( f: HOLFormula, sub: Substitution ): HOLFormula = betaNormalize( sub( f ) )
  def bnsub( f: Label, sub: Substitution ): Label = f.map( bnsub( _, sub ) )
  def bnsub( f: LabelledFormula, sub: Substitution ): LabelledFormula = ( bnsub( f._1, sub ), bnsub( f._2, sub ) )
}

/*
object applySubstitution {
  def apply( l: Label)(implicit subst : Substitution) : Label = l map subst.apply
  def apply( s : LabelledFormula)(implicit subst : Substitution) : LabelledFormula = (apply(s._1)(subst), subst(s._2))
  def apply( s : LabelledSequent)(implicit subst : Substitution) : LabelledSequent= s.map(apply)

  def apply( proof: LKskProof, cut_ancs: Sequent[Boolean])(implicit subst : Substitution): ( LKskProof, Sequent[Boolean] ) = {
    /* Invariant of the algorithm: in proof and subst(proof), the sequent index of each formula F and subst(F) is the same
       as a consequence, also cut_ancs == subst(cut_ancs). It is still present in the signature s.t. the ceres omega code
       does not rely on the invariant.
    */
    implicit val c_ancs = cut_ancs
    proof.occConnectors
    try {
      val r: ( LKskProof, Sequent[Boolean] ) = proof match {
        /* Structural rules except cut */
        case TopRight( _ ) | BottomLeft( _ ) => (proof, cut_ancs)
        case Axiom( l1, l2, f ) => (Axiom(apply(l1), apply(l2), subst(f)), cut_ancs )
        case Reflexivity( l, f )                =>
          (Reflexivity(apply(l), subst(f)), cut_ancs )
        case ContractionLeft( p, a1, a2 )       =>
          val (rp, _) = apply(p, cut_ancs)
          (ContractionLeft(rp,a1,a2), cut_ancs)
        case ContractionRight( p, a1, a2 )      =>
          val (rp, _) = apply(p, cut_ancs)
          (ContractionRight(rp, a1, a2), cut_ancs)
        case WeakeningLeft( p, m )              =>
          val (rp, _) = apply(rp, cut_ancs)
          (WeakeningLeft(p,m), cut_ancs)
        case WeakeningRight( p, m )             =>
          val (rp, _) = apply(p, cut_ancs)
          (WeakeningRight(rp,m), cut_ancs)

        /* Logical rules */
        case AndRight( p1, a1, p2, a2 )         =>
          val (rp1, _) = apply(p1, cut_ancs)
          val (rp2, _) = apply(p2, cut_ancs)
          (AndRight(rp1,a1,rp2,a2), cut_ancs)
        case OrLeft( p1, a1, p2, a2 )           =>
          val (rp1, _) = apply(p1, cut_ancs)
          val (rp2, _) = apply(p2, cut_ancs)
          (OrLeft(rp1,a1,rp2,a2), cut_ancs)
        case ImpLeft( p1, a1, p2, a2 )          =>
          val (rp1, _) = apply(p1, cut_ancs)
          val (rp2, _) = apply(p2, cut_ancs)
          (ImpLeft(rp1,a1,rp2,a2), cut_ancs)
        case NegLeft( p, a )                    =>
          val (rp, _) = apply(p, cut_ancs)
          (NegLeft(rp,a), cut_ancs)
        case NegRight( p, a )                   =>
          val (rp, _) = apply(p, cut_ancs)
          (NegRight(rp,a), cut_ancs)
        case OrRight( p, a1, a2 )               =>
          val (rp, _) = apply(p, cut_ancs)
          (OrRight(rp, a1,a2), cut_ancs)
        case AndLeft( p, a1, a2 )               =>
          val (rp, _) = apply(p, cut_ancs)
          (AndLeft(rp,a1,a2), cut_ancs)
        case ImpRight( p, a1, a2 )              =>
          val (rp, _) = apply(p, cut_ancs)
          (ImpRight(rp,a1,a2), cut_ancs)

        /* quantifier rules  */
        case AllRight( p, a, f, eigenvar ) if subst.range contains eigenvar =>
          val ev = rename(ev, subst.range)
          val (rp1, _) = apply(p, cut_ancs)(Substitution(eigenvar -> ev))
          val (rp2, _) = AllRight(rp1, a, f, ev)
          apply(rp2, cut_ancs)
        case AllRight(p,a,f,eigenvar) =>
          val (rp,_) = apply(p, cut_ancs)(Substitution(subst.map - eigenvar))
          (AllRight(rp, a, betaNormalize(subst(f)), eigenvar), cut_ancs)
        case ExLeft( p, a, f, eigenvar ) if subst.range contains eigenvar    =>
          val ev = rename(ev, subst.range)
          val (rp1, _) = apply(p, cut_ancs)(Substitution(eigenvar -> ev))
          val (rp2, _) = ExLeft(rp1, a, f, ev)
          apply(rp2, cut_ancs)
        case ExLeft( p, a, f, eigenvar )     =>
          val (rp,_) = apply(p, cut_ancs)(Substitution(subst.map - eigenvar))
          (ExLeft(rp, a, betaNormalize(subst(f)), eigenvar), cut_ancs)

        case AllLeft( p, a, f, t )              =>
          val (rp,_) = apply(p, cut_ancs)
          (AllLeft(rp, a, betaNormalize(subst(f)), betaNormalize(subst(t))), cut_ancs)
        case ExRight( p, a, f, t )              =>
          val (rp,_) = apply(p, cut_ancs)
          (ExRight(rp, a, betaNormalize(subst(f)), betaNormalize(subst(t))), cut_ancs)

        case AllSkRight( p, a, main, sk_const ) =>
          val (rp,_) = apply(p, cut_ancs)
          (AllSkRight(rp, a, betaNormalize(subst(main)), sk_const), cut_ancs)
        case ExSkLeft( p, a, main, sk_const )   =>
          val (rp,_) = apply(p, cut_ancs)
          (ExSkLeft(rp, a, betaNormalize(subst(main)), sk_const), cut_ancs)
        case AllSkLeft( p, a, f, t )            =>
          val (rp,_) = apply(p, cut_ancs)
          (AllSkLeft(rp, a, betaNormalize(subst(f)), betaNormalize(subst(t))), cut_ancs)
        case ExSkRight( p, a, f, t )            =>
          val (rp,_) = apply(p, cut_ancs)
          (ExSkRight(rp, a, betaNormalize(subst(f)), betaNormalize(subst(t))), cut_ancs)

        case Equality( p, e, a, flipped, pos ) =>
          val (rp, _) = apply(p, cut_ancs)
          (Equality(rp,e,a,flipped,pos), cut_ancs)

        case r @ Cut( p1, a1, p2, a2 ) =>
        case _ => throw new Exception( "No such a rule in Projections.apply " + proof.longName )
      }
      r
    } catch {
      case e: ProjectionException =>
        //println("passing exception up...")
        //throw ProjectionException(e.getMessage, proof, Nil, null)
        throw e
      case e: Exception =>
        throw ProjectionException( "Error computing projection: " + e.getMessage + sys.props( "line.separator" ) + e.getStackTrace, proof, Nil, e )
    }
  }
}
*/
