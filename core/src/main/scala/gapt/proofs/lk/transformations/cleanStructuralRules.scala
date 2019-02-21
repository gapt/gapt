package gapt.proofs.lk.transformations

import gapt.proofs.Ant
import gapt.proofs.SequentConnector
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ConversionLeftRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionCase
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule

object cleanStructuralRules {
  /**
   * "Cleans up" a proof by permuting weakenings downward as far as possible.
   *
   * @param proof The LKProof to be transformed.
   * @param reductive Whether the algorithm is allowed to discard "unnecessary" subproofs. True by default.
   * @return A proof of the same end sequent (up to a permutation) in which all weakenings are
   *         performed as late as possible.
   */
  def apply( proof: LKProof, reductive: Boolean = true ): LKProof = withSequentConnector( proof, reductive )._1

  /**
   * "Cleans up" a proof by permuting weakenings downward as far as possible.
   *
   * @param proof The LKProof to be transformed.
   * @param reductive Whether the algorithm is allowed to discard "unnecessary" subproofs. True by default.
   * @return A proof of the same end sequent (up to a permutation) in which all weakenings are
   *         performed as late as possible;
   *         and an SequentConnector relating the end sequents of the old and new proofs.
   */
  def withSequentConnector( proof: LKProof, reductive: Boolean = true ): ( LKProof, SequentConnector ) = {
    val ( subProof, connector ) = apply_( proof, reductive )
    introduceWeakenings( proof, subProof, connector, proof.endSequent.indices )
  }

  /**
   * Performs the actual proof transformation.
   *
   * @param proof An LKProof.
   * @param reductive Whether the algorithm is allowed to discard "unnecessary" subproofs. True by default.
   * @return A new LKProof proofNew and an SequentConnector conn relating the end sequent of
   *         the old and new proofs in the following
   *         manner: If i is an index of the end sequent of proof, then conn.child(i) is the
   *         index of the corresponding formula
   *         occurrence in the end sequent of proofNew. If conn.child(i) is empty,
   *         then the occurrence was "weak" in the
   *         old proof and its introduction has not happened yet in the new proof.
   */
  private def apply_( proof: LKProof, reductive: Boolean ): ( LKProof, SequentConnector ) = proof match {
    case InitialSequent( sequent ) =>
      ( proof, SequentConnector( sequent ) )

    case p @ WeakeningLeftRule( subProof, formula ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )
      ( subProofNew, subConnector * p.getSequentConnector.inv )

    case p @ WeakeningRightRule( subProof, formula ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )
      ( subProofNew, subConnector * p.getSequentConnector.inv )

    case p @ ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) => // The contraction is performed on two non-weak occurrences → just do it
          val proofNew = ContractionLeftRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // At least one of the occurrences is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {
        case ( Seq( a1 ), Seq( a2 ) ) => // The contraction is performed on two non-weak occurrences → just do it
          val proofNew = ContractionRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // At least one of the occurrences is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply_( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply_( rightSubProof, reductive )

      if ( reductive ) // We may throw away subproofs
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {

          case ( Seq( a1 ), Seq( a2 ) ) => // Neither cut formula is weak → just do it
            val proofNew = CutRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftSequentConnector * leftSubConnector * p.getLeftSequentConnector.inv )
              + ( proofNew.getRightSequentConnector * rightSubConnector * p.getRightSequentConnector.inv ) )

          case ( Seq(), _ ) => // The left cut formula is weak → throw away the right proof
            ( leftSubProofNew, leftSubConnector * p.getLeftSequentConnector.inv )

          case ( Seq( a1 ), Seq() ) => // The right cut formula is weak → throw away the left proof
            ( rightSubProofNew, rightSubConnector * p.getRightSequentConnector.inv )
        }

      else { // Not allowed to throw away subproofs, so we have to perform some weakenings
        val ( leftSubProofNew_, leftSubConnector_ ) =
          introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) =
          introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = CutRule( leftSubProofNew_, leftSubConnector_.child( aux1 ),
          rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftSequentConnector * leftSubConnector_ * p.getLeftSequentConnector.inv )
          + ( proofNew.getRightSequentConnector * rightSubConnector_ * p.getRightSequentConnector.inv ) )
      }

    case p @ InductionRule( cases, main, term ) =>

      if ( cases.isEmpty )
        ( p, SequentConnector( p.endSequent ) )

      else {
        // First run the algorithm on all induction cases
        val ( subProofsNew, subConnectors ) = cases.map { c => apply_( c.proof, reductive ) }.unzip

        // Tests whether the ith induction case is "weak", i.e. all hypotheses and the conclusion are weak.
        def isWeak( i: Int ): Boolean = {
          val weakHypos = for ( h <- cases( i ).hypotheses ) yield subConnectors( i ).children( h ).isEmpty
          weakHypos.forall( _ == true ) && subConnectors( i ).children( cases( i ).conclusion ).isEmpty
        }

        // Find the first weak induction case
        val weakIndex = cases.indices.find( isWeak )

        if ( reductive && weakIndex.nonEmpty ) {
          // We may throw away subproofs and there is a weak case → throw away everything else
          val i = weakIndex.get
          val ( subProofNew, subConnector ) = ( subProofsNew( i ), subConnectors( i ) )

          ( subProofNew, subConnector * p.occConnectors( i ).inv )

        } else { // Not allowed to throw away subproofs, so we have to perform some weakenings
          val ( casesNew, subConnectorsNew ) = ( for ( i <- cases.indices ) yield {
            val c = cases( i )
            val ( subProofNew, subConnector ) = ( subProofsNew( i ), subConnectors( i ) )
            val ( subProofNew_, subConnector_ ) =
              introduceWeakenings( c.proof, subProofNew, subConnector, c.hypotheses :+ c.conclusion )
            val hypothesesNew = c.hypotheses map { h => subConnector_.child( h ) }
            val conclusionNew = subConnector_.child( c.conclusion )

            ( InductionCase( subProofNew_, c.constructor, hypothesesNew, c.eigenVars, conclusionNew ), subConnector_ )
          } ).unzip

          val proofNew = InductionRule( casesNew, main, term )
          val occConnectorsNew = for ( i <- p.immediateSubProofs.indices )
            yield proofNew.occConnectors( i ) * subConnectorsNew( i ) * p.occConnectors( i ).inv

          val occConnectorNew = occConnectorsNew.reduceLeft( _ + _ )
          ( proofNew, occConnectorNew )
        }
      }

    case p @ NegLeftRule( subProof, aux ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match { // The negation is performed on a non-weak formula → just do it
        case Seq( a ) =>
          val proofNew = NegLeftRule( subProofNew, a )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ NegRightRule( subProof, aux ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {
        case Seq( a ) => // The negation is performed on a non-weak formula → just do it
          val proofNew = NegRightRule( subProofNew, a )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {

        case ( Seq( a1 ), Seq( a2 ) ) => // Neither conjunct is weak → just perform the inference
          val proofNew = AndLeftRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case ( Seq(), Seq() ) => // Both conjuncts are weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )

        case _ => // One conjunct is weak → perform the weakening, then the ∧:l inference
          val ( subProofNew_, subConnector_ ) =
            introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = AndLeftRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getSequentConnector * subConnector_ * p.getSequentConnector.inv )
      }

    case p @ AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply_( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply_( rightSubProof, reductive )

      if ( reductive ) // We may throw away subproofs
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {

          case ( Seq( a1 ), Seq( a2 ) ) => // Neither conjunct is weak → just do it
            val proofNew = AndRightRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftSequentConnector * leftSubConnector * p.getLeftSequentConnector.inv )
              + ( proofNew.getRightSequentConnector * rightSubConnector * p.getRightSequentConnector.inv ) )

          case ( Seq(), _ ) => // The left conjunct is weak → throw away the right proof
            ( leftSubProofNew, leftSubConnector * p.getLeftSequentConnector.inv )

          case ( Seq( a1 ), Seq() ) => // The right conjunct is weak → throw away the left proof
            ( rightSubProofNew, rightSubConnector * p.getRightSequentConnector.inv )
        }

      else { // Not allowed to throw away subproofs, so we have to perform some weakenings
        val ( leftSubProofNew_, leftSubConnector_ ) =
          introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) =
          introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = AndRightRule( leftSubProofNew_, leftSubConnector_.child( aux1 ),
          rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftSequentConnector * leftSubConnector_ * p.getLeftSequentConnector.inv )
          + ( proofNew.getRightSequentConnector * rightSubConnector_ * p.getRightSequentConnector.inv ) )
      }

    case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply_( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply_( rightSubProof, reductive )

      if ( reductive ) // We may throw away subproofs
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {

          case ( Seq( a1 ), Seq( a2 ) ) => // Neither disjunct is weak → just do it
            val proofNew = OrLeftRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftSequentConnector * leftSubConnector * p.getLeftSequentConnector.inv )
              + ( proofNew.getRightSequentConnector * rightSubConnector * p.getRightSequentConnector.inv ) )

          case ( Seq(), _ ) => // The left disjunct is weak → throw away the right proof
            ( leftSubProofNew, leftSubConnector * p.getLeftSequentConnector.inv )

          case ( Seq( a1 ), Seq() ) => // The right disjunct is weak → throw away the left proof
            ( rightSubProofNew, rightSubConnector * p.getRightSequentConnector.inv )
        }

      else { // Not allowed to throw away subproofs, so we have to perform some weakenings
        val ( leftSubProofNew_, leftSubConnector_ ) =
          introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) =
          introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = OrLeftRule( leftSubProofNew_, leftSubConnector_.child( aux1 ),
          rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftSequentConnector * leftSubConnector_ * p.getLeftSequentConnector.inv )
          + ( proofNew.getRightSequentConnector * rightSubConnector_ * p.getRightSequentConnector.inv ) )
      }

    case p @ OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {

        case ( Seq( a1 ), Seq( a2 ) ) => // Neither disjunct is weak → just perform the inference
          val proofNew = OrRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case ( Seq(), Seq() ) => // Both disjuncts are weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )

        case _ => // One disjunct is weak → perform the weakening, then the ∨:r inference
          val ( subProofNew_, subConnector_ ) =
            introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = OrRightRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getSequentConnector * subConnector_ * p.getSequentConnector.inv )
      }

    case p @ ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofNew, leftSubConnector ) = apply_( leftSubProof, reductive )
      val ( rightSubProofNew, rightSubConnector ) = apply_( rightSubProof, reductive )

      if ( reductive ) // We may throw away subproofs
        ( leftSubConnector.children( aux1 ), rightSubConnector.children( aux2 ) ) match {

          case ( Seq( a1 ), Seq( a2 ) ) => // Neither aux formula is weak → just do it
            val proofNew = ImpLeftRule( leftSubProofNew, a1, rightSubProofNew, a2 )
            ( proofNew,
              ( proofNew.getLeftSequentConnector * leftSubConnector * p.getLeftSequentConnector.inv )
              + ( proofNew.getRightSequentConnector * rightSubConnector * p.getRightSequentConnector.inv ) )

          case ( Seq(), _ ) => // The premise is weak → throw away the right proof
            ( leftSubProofNew, leftSubConnector * p.getLeftSequentConnector.inv )

          case ( Seq( a1 ), Seq() ) => // The conclusion is weak → throw away the left proof
            ( rightSubProofNew, rightSubConnector * p.getRightSequentConnector.inv )
        }

      else { // Not allowed to throw away subproofs, so we have to perform some weakenings
        val ( leftSubProofNew_, leftSubConnector_ ) =
          introduceWeakenings( leftSubProof, leftSubProofNew, leftSubConnector, Seq( aux1 ) )
        val ( rightSubProofNew_, rightSubConnector_ ) =
          introduceWeakenings( rightSubProof, rightSubProofNew, rightSubConnector, Seq( aux2 ) )

        val proofNew = ImpLeftRule( leftSubProofNew_, leftSubConnector_.child( aux1 ),
          rightSubProofNew_, rightSubConnector_.child( aux2 ) )

        ( proofNew, ( proofNew.getLeftSequentConnector * leftSubConnector_ * p.getLeftSequentConnector.inv )
          + ( proofNew.getRightSequentConnector * rightSubConnector_ * p.getRightSequentConnector.inv ) )
      }

    case p @ ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      ( subConnector.children( aux1 ), subConnector.children( aux2 ) ) match {

        case ( Seq( a1 ), Seq( a2 ) ) => // Neither disjunct is weak → just perform the inference
          val proofNew = ImpRightRule( subProofNew, a1, a2 )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case ( Seq(), Seq() ) => // Both aux formulas are weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )

        case _ => // One aux formula is weak → perform the weakening, then the →:r inference
          val ( subProofNew_, subConnector_ ) =
            introduceWeakenings( subProof, subProofNew, subConnector, Seq( aux1, aux2 ) )
          val proofNew = ImpRightRule( subProofNew_, subConnector_.child( aux1 ), subConnector_.child( aux2 ) )
          ( proofNew, proofNew.getSequentConnector * subConnector_ * p.getSequentConnector.inv )
      }

    case p @ ForallLeftRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ForallLeftRule( subProofNew, a, f, term, v )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ForallRightRule( subProofNew, a, eigen, quant )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ForallSkRightRule( subProof, aux, main, skTerm ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ForallSkRightRule( subProofNew, a, main, skTerm )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ExistsLeftRule( subProofNew, a, eigen, quant )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ExistsSkLeftRule( subProof, aux, main, skTerm ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ExistsSkLeftRule( subProofNew, a, main, skTerm )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ExistsRightRule( subProof, aux, f, term, v ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ExistsRightRule( subProofNew, a, f, term, v )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ EqualityLeftRule( subProof, eq, aux, con ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq() => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )

        case _ =>
          // The aux formula is not weak → introduce the equation by weakening,
          // if necessary, then perform the inference
          val ( subProofNew_, subConnector_ ) =
            introduceWeakenings( subProof, subProofNew, subConnector, Seq( eq ) )
          val proofNew = EqualityLeftRule( subProofNew_, subConnector_.child( eq ), subConnector_.child( aux ), con )
          ( proofNew, proofNew.getSequentConnector * subConnector_ * p.getSequentConnector.inv )
      }

    case p @ EqualityRightRule( subProof, eq, aux, con ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq() => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )

        case _ =>
          // The aux formula is not weak → introduce the equation by weakening,
          // if necessary, then perform the inference
          val ( subProofNew_, subConnector_ ) = introduceWeakenings( subProof, subProofNew, subConnector, Seq( eq ) )
          val proofNew = EqualityRightRule( subProofNew_, subConnector_.child( eq ), subConnector_.child( aux ), con )
          ( proofNew, proofNew.getSequentConnector * subConnector_ * p.getSequentConnector.inv )
      }

    case p @ ConversionLeftRule( subProof, aux, main ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ConversionLeftRule( subProofNew, a, main )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }

    case p @ ConversionRightRule( subProof, aux, main ) =>
      val ( subProofNew, subConnector ) = apply_( subProof, reductive )

      subConnector.children( aux ) match {

        case Seq( a ) => // The inference is performed on a non-weak formula → just do it
          val proofNew = ConversionRightRule( subProofNew, a, main )
          ( proofNew, proofNew.getSequentConnector * subConnector * p.getSequentConnector.inv )

        case _ => // The aux formula is weak → do nothing
          ( subProofNew, subConnector * p.getSequentConnector.inv )
      }
  }

  /**
   *
   * @param subProofOld An LKProof.
   * @param subProofNew The corresponding proof after removing unnecessary weakenings.
   * @param subConnector An SequentConnector relating subProofOld and subProofNew.
   * @param toBeIntroduced The list of indices of formulas that should be introduced by weakening, if necessary.
   * @return A pair consisting of an LKProof proofNew and an SequentConnector conn such that:
   *         1) proofNew is subProofNew extended with 0 or more weakenings;
   *         2) conn relates subProofOld and proofNew;
   *         3)for each i in toBeIntroduced,conn.child(i) is nonempty.
   */
  private def introduceWeakenings( subProofOld: LKProof, subProofNew: LKProof,
                                   subConnector:   SequentConnector,
                                   toBeIntroduced: Seq[SequentIndex] ): ( LKProof, SequentConnector ) = {
    val premise = subProofOld.endSequent

    ( ( subProofNew, subConnector ) /: toBeIntroduced ) { ( acc, idx ) =>
      // Iterate over toBeIntroduced, generating a new subproof and connector in each step
      val ( currentProof, currentOC ) = acc

      if ( currentOC.children( idx ).nonEmpty )
        // If the index already has a descendant, we don't need to perform a weakening
        ( currentProof, currentOC )

      else {
        val proofNew = idx match { // Perform a weakening on the correct side

          case Ant( _ ) =>
            WeakeningLeftRule( currentProof, premise( idx ) )

          case Suc( _ ) =>
            WeakeningRightRule( currentProof, premise( idx ) )
        }

        // Hook up the SequentConnector properly
        val oc = proofNew.getSequentConnector
        val mainIdx = proofNew.mainIndices.head
        ( proofNew, ( oc * currentOC ) + ( mainIdx, idx ) )
      }
    }
  }

}
