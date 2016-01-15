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
      val renamedEigen = rename( eigen, substitution.range )
      val renamed_proof = apply( Substitution( eigen -> renamedEigen ), preserveEigenvariables )( subProof )
      apply( substitution, preserveEigenvariables )( AllRight( renamed_proof, aux, bnsub( formula, substitution ), renamedEigen ) )

    case p @ AllRight( subProof, aux, formula, eigen ) =>
      val renamed_main @ All( newQuant, _ ) = bnsub( p.mainFormula, substitution )
      val renamed_proof = apply( Substitution( substitution.map - eigen ) )( subProof )
      AllRight( renamed_proof, aux, renamed_main, newQuant )

    case ExLeft( subProof, aux, formula, eigen ) if substitution.range contains eigen =>
      require( !preserveEigenvariables, s"Cannot apply substitution: Eigenvariable $eigen is in range of substitution" )
      val renamedEigen = rename( eigen, substitution.range )
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

    case _ => throw new IllegalArgumentException( s"This rule is not handled at this time." )
  }

  def bnsub( f: LambdaExpression, sub: Substitution ): LambdaExpression = betaNormalize( sub( f ) )
  def bnsub( f: HOLFormula, sub: Substitution ): HOLFormula = betaNormalize( sub( f ) )
  def bnsub( f: Label, sub: Substitution ): Label = f.map( bnsub( _, sub ) )
  def bnsub( f: LabelledFormula, sub: Substitution ): LabelledFormula = ( bnsub( f._1, sub ), bnsub( f._2, sub ) )
}
