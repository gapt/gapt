package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ HOLPosition, isPrenex, instantiate }
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.{ HOLSequent, Suc, Ant, SequentIndex }

object AndLeftMacroRule extends RuleConvenienceObject( "AndLeftMacroRule" ) {
  def apply( subProof: LKProof, leftConjunct: HOLFormula, rightConjunct: HOLFormula ): LKProof = {
    val ( indices, _ ) = findFormulasInPremise( subProof.endSequent )( Seq( leftConjunct, rightConjunct ), Seq() )
    indices match {
      case -1 +: -1 +: _ => throw LKRuleCreationException( s"Neither $leftConjunct nor $rightConjunct has been found in antecedent of ${subProof.endSequent}." )

      case -1 +: _ +: _ => // The right conjunct has been found.
        AndLeftRule( WeakeningLeftRule( subProof, leftConjunct ), leftConjunct, rightConjunct )

      case _ +: -1 +: _ => // The left conjunct has been found.
        AndLeftRule( WeakeningLeftRule( subProof, rightConjunct ), leftConjunct, rightConjunct )

      case _ => AndLeftRule( subProof, leftConjunct, rightConjunct )
    }
  }
}

object OrRightMacroRule extends RuleConvenienceObject( "OrRightMacroRule" ) {
  def apply( subProof: LKProof, leftDisjunct: HOLFormula, rightDisjunct: HOLFormula ): LKProof = {
    val ( _, indices ) = findFormulasInPremise( subProof.endSequent )( Seq(), Seq( leftDisjunct, rightDisjunct ) )
    indices match {
      case -1 +: -1 +: _ => throw LKRuleCreationException( s"Neither $leftDisjunct nor $rightDisjunct has been found in succedent of ${subProof.endSequent}." )

      case -1 +: _ +: _ => // The right disjunct has been found.
        OrRightRule( WeakeningRightRule( subProof, leftDisjunct ), leftDisjunct, rightDisjunct )

      case _ +: -1 +: _ => // The left conjunct has been found.
        OrRightRule( WeakeningRightRule( subProof, rightDisjunct ), leftDisjunct, rightDisjunct )

      case _ => OrRightRule( subProof, leftDisjunct, rightDisjunct )
    }
  }
}

object TransRule {
  /**
   * <pre>Performs a proof employing transitivity.
   *
   * Takes a proof π with end-sequent of the form
   * (x=z), Trans, ... |- ...
   * and return one with end-sequent of the form
   * (x=y), (y=z), Trans, ... |- ...
   * where Trans is defined as Forall xyz.((x=y ∧ y=z) -> x=z)
   * </pre>
   * @param x X
   * @param y Y
   * @param z Z
   * @param subProof The proof π which contains the (x=z) which is to be shown.
   * @return A proof with π as a subtree and the formula (x=z) replaced by (x=y) and (y=z).
   */
  def apply( x: FOLTerm, y: FOLTerm, z: FOLTerm, subProof: LKProof ): LKProof = {

    val xv = FOLVar( "x" )
    val yv = FOLVar( "y" )
    val zv = FOLVar( "z" )

    //Forall xyz.(x = y ^ y = z -> x = z)
    val Trans = All( xv, All( yv, All( zv, Imp( And( Eq( xv, yv ), Eq( yv, zv ) ), Eq( xv, zv ) ) ) ) )
    def TransX( x: FOLTerm ) = All( yv, All( zv, Imp( And( Eq( x, yv ), Eq( yv, zv ) ), Eq( x, zv ) ) ) )
    def TransXY( x: FOLTerm, y: FOLTerm ) = All( zv, Imp( And( Eq( x, y ), Eq( y, zv ) ), Eq( x, zv ) ) )
    def TransXYZ( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) )

    val xy = Eq( x, y )
    val yz = Eq( y, z )
    val xz = Eq( x, z )

    val ax_xy = LogicalAxiom( xy )
    val ax_yz = LogicalAxiom( yz )

    val s1 = AndRightRule( ax_xy, xy, ax_yz, yz )

    val imp = ImpLeftRule( s1, And( xy, yz ), subProof, xz )

    val allQZ = ForallLeftRule( imp, TransXY( x, y ), z )
    val allQYZ = ForallLeftRule( allQZ, TransX( x ), y )
    val allQXYZ = ForallLeftRule( allQYZ, Trans, x )

    ContractionLeftRule( allQXYZ, Trans )
  }
}

object ForallLeftBlock {
  /**
   * Applies the ForallLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *                (π)
   *  A[x1\term1,...,xN\termN], Γ :- Δ
   * ---------------------------------- (∀_l x n)
   *       ∀ x1,..,xN.A, Γ :- Δ
   * </pre>
   *
   * @param subProof The top proof with (sL, A[x1\term1,...,xN\termN] :- sR) as the bottommost sequent.
   * @param main A formula of the form (Forall x1,...,xN.A).
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, terms: Seq[LambdaExpression] ): LKProof = withOccConnector( subProof, main, terms )._1

  def withOccConnector( subProof: LKProof, main: HOLFormula, terms: Seq[LambdaExpression] ): ( LKProof, OccConnector ) = {
    val partiallyInstantiatedMains = ( 0 to terms.length ).toList.reverse.map( n => instantiate( main, terms.take( n ) ) )

    val series = terms.reverse.foldLeft( ( subProof, partiallyInstantiatedMains, OccConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
      val newSubProof = ForallLeftRule( acc._1, acc._2.tail.head, ai )
      val newOccConnector = newSubProof.getOccConnector * acc._3
      ( newSubProof, acc._2.tail, newOccConnector )
    }

    ( series._1, series._3 )
  }
}

object ForallRightBlock {
  /**
   * Applies the ForallRight-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the right side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *              (π)
   *    Γ :- Δ, A[x1\y1,...,xN\yN]
   * ---------------------------------- (∀_r x n)
   *     Γ :- Δ, ∀x1,..,xN.A
   *
   * where y1,...,yN are eigenvariables.
   * </pre>
   *
   * @param subProof The proof π with (Γ :- Δ, A[x1\y1,...,xN\yN]) as the bottommost sequent.
   * @param main A formula of the form (∀ x1,...,xN.A).
   * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, eigenvariables: Seq[Var] ): LKProof = withOccConnector( subProof, main, eigenvariables )._1

  def withOccConnector( subProof: LKProof, main: HOLFormula, eigenvariables: Seq[Var] ): ( LKProof, OccConnector ) = {
    val partiallyInstantiatedMains = ( 0 to eigenvariables.length ).toList.reverse.map( n => instantiate( main, eigenvariables.take( n ) ) )

    val series = eigenvariables.reverse.foldLeft( ( subProof, partiallyInstantiatedMains, OccConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
      val newSubProof = ForallRightRule( acc._1, acc._2.tail.head, ai )
      val newOccConnector = newSubProof.getOccConnector * acc._3
      ( newSubProof, acc._2.tail, newOccConnector )
    }

    ( series._1, series._3 )
  }
}

object ExistsLeftBlock {
  /**
   * Applies the ExistsLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *              (π)
   *    A[x1\y1,...,xN\yN], Γ :- Δ
   * ---------------------------------- (∀_r x n)
   *     ∃x1,..,xN.A, Γ :- Δ
   *
   * where y1,...,yN are eigenvariables.
   * </pre>
   *
   * @param subProof The proof π with (A[x1\y1,...,xN\yN], Γ :- Δ) as the bottommost sequent.
   * @param main A formula of the form (∃ x1,...,xN.A).
   * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, eigenvariables: Seq[Var] ): LKProof = withOccConnector( subProof, main, eigenvariables )._1

  def withOccConnector( subProof: LKProof, main: HOLFormula, eigenvariables: Seq[Var] ): ( LKProof, OccConnector ) = {
    val partiallyInstantiatedMains = ( 0 to eigenvariables.length ).toList.reverse.map( n => instantiate( main, eigenvariables.take( n ) ) )

    val series = eigenvariables.reverse.foldLeft( ( subProof, partiallyInstantiatedMains, OccConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
      val newSubProof = ExistsLeftRule( acc._1, acc._2.tail.head, ai )
      val newOccConnector = newSubProof.getOccConnector * acc._3
      ( newSubProof, acc._2.tail, newOccConnector )
    }

    ( series._1, series._3 )
  }
}

object ExistsRightBlock {
  /**
   * Applies the ExistsRight-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the right side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *                (π)
   *  Γ :- Δ, A[x1\term1,...,xN\termN]
   * ---------------------------------- (∀_l x n)
   *       Γ :- Δ, ∃ x1,..,xN.A
   * </pre>
   *
   * @param subProof The top proof with (Γ :- Δ, A[x1\term1,...,xN\termN]) as the bottommost sequent.
   * @param main A formula of the form (∃ x1,...,xN.A).
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: HOLFormula, terms: Seq[LambdaExpression] ): LKProof = withOccConnector( subProof, main, terms )._1

  def withOccConnector( subProof: LKProof, main: HOLFormula, terms: Seq[LambdaExpression] ): ( LKProof, OccConnector ) = {
    val partiallyInstantiatedMains = ( 0 to terms.length ).toList.reverse.map( n => instantiate( main, terms.take( n ) ) )

    val series = terms.reverse.foldLeft( ( subProof, partiallyInstantiatedMains, OccConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
      val newSubProof = ExistsRightRule( acc._1, acc._2.tail.head, ai )
      val newOccConnector = newSubProof.getOccConnector * acc._3
      ( newSubProof, acc._2.tail, newOccConnector )
    }

    ( series._1, series._3 )
  }
}

/**
 * This macro rule simulates a series of contractions in the antecedent.
 *
 */
object ContractionLeftMacroRule {

  /**
   *
   * @param p A proof.
   * @param occs A list of occurrences of a Formula in the antecedent of s1.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a single occurrence.
   */
  def apply( p: LKProof, occs: Seq[SequentIndex] ): LKProof = occs match {
    case Seq() | _ +: Seq() => p
    case occ1 +: occ2 +: rest =>
      val subProof = ContractionLeftRule( p, occ1, occ2 )
      ContractionLeftMacroRule( subProof, subProof.mainIndices.head +: rest )
  }

  /**
   * Contracts one formula in the antecedent down to n occurrences. Use with care!
   *
   * @param p A proof.
   * @param form A formula.
   * @param n Maximum number of occurrences of form in the antecedent of the end sequent. Defaults to 1, i.e. all occurrences are contracted.
   * @return
   */
  def apply( p: LKProof, form: HOLFormula, n: Int = 1 ): LKProof = {
    if ( n < 1 ) throw new IllegalArgumentException( "n must be >= 1." )
    val list = p.endSequent.indicesWhere( _ == form ).collect { case i: Ant => i }.drop( n - 1 ).reverse

    apply( p, list )
  }
}

/**
 * This macro rule simulates a series of contractions in the succedent.
 *
 */
object ContractionRightMacroRule {

  /**
   *
   * @param p A proof.
   * @param occs A list of occurrences of a formula in the succedent of s1.
   * @return A proof ending with as many contraction rules as necessary to contract occs into a single occurrence.
   */
  def apply( p: LKProof, occs: Seq[SequentIndex] ): LKProof = occs match {
    case Seq() | _ +: Seq() => p
    case occ1 +: occ2 +: rest =>
      val subProof = ContractionRightRule( p, occ1, occ2 )
      ContractionRightMacroRule( subProof, subProof.mainIndices.head +: rest )
  }

  /**
   * Contracts one formula in the succedent down to n occurrences. Use with care!
   *
   * @param p A proof.
   * @param form A formula.
   * @param n Maximum number of occurrences of form in the succedent of the end sequent. Defaults to 1, i.e. all occurrences are contracted.
   * @return
   */
  def apply( p: LKProof, form: HOLFormula, n: Int = 1 ): LKProof = {
    if ( n < 1 ) throw new IllegalArgumentException( "n must be >= 1." )
    val list = p.endSequent.indicesWhere( _ == form ).collect { case i: Suc => i }.drop( n - 1 ).reverse

    apply( p, list )
  }
}

/**
 * This macro rule simulates a series of contractions in both cedents.
 *
 */
object ContractionMacroRule extends RuleConvenienceObject( "ContractionMacroRule" ) {

  /**
   * Contracts the current proof down to a given sequent.
   *
   * @param p An LKProof.
   * @param targetSequent The target sequent.
   * @param strict If true, the end sequent of p must 1.) contain every formula at least as often as targetSequent
   *               and 2.) contain no formula that isn't contained at least once in targetSequent.
   * @return s1 with its end sequent contracted down to targetSequent.
   */
  def apply( p: LKProof, targetSequent: HOLSequent, strict: Boolean = true ): LKProof = {
    val currentSequent = p.endSequent
    val targetAnt = targetSequent.antecedent
    val targetSuc = targetSequent.succedent

    val assertion = ( ( targetSequent isSubMultisetOf currentSequent )
      && ( currentSequent isSubsetOf targetSequent ) )

    if ( strict & !assertion ) {
      throw LKRuleCreationException( "Sequent " + targetSequent + " cannot be reached from " + currentSequent + " by contractions." )
    }

    val subProof = targetAnt.distinct.foldLeft( p )( ( acc, x ) => { ContractionLeftMacroRule( acc, x, targetAnt.count( _ == x ) ) } )
    targetSuc.distinct.foldLeft( subProof )( ( acc, x ) => { ContractionRightMacroRule( acc, x, targetSuc.count( _ == x ) ) } )
  }

  /**
   * Performs all possible contractions. Use with care!
   *
   * @param p A proof.
   * @return A proof with all duplicate formulas in the end sequent contracted.
   */
  def apply( p: LKProof ): LKProof = {
    val targetSequent = p.endSequent.distinct
    apply( p, targetSequent )
  }

}

/**
 * This macro rule simulates a series of weakenings in the antecedent.
 *
 */
object WeakeningLeftMacroRule {

  /**
   *
   * @param p A proof.
   * @param formulas A list of formulas.
   * @return A new proof whose antecedent contains new occurrences of the formulas in formulas.
   */
  def apply( p: LKProof, formulas: Seq[HOLFormula] ): LKProof =
    formulas.foldLeft( p ) { ( acc, x ) => WeakeningLeftRule( acc, x ) }

  /**
   *
   * @param p An LKProof.
   * @param formula A Formula.
   * @param n A natural number.
   * @return p extended with weakenings such that formula occurs at least n times in the antecedent of the end sequent.
   */
  def apply( p: LKProof, formula: HOLFormula, n: Int ): LKProof = {
    val nCurrent = p.endSequent.antecedent.count( _ == formula )

    WeakeningLeftMacroRule( p, Seq.fill( n - nCurrent )( formula ) )
  }
}

/**
 * This macro rule simulates a series of weakenings in the succedent.
 *
 */
object WeakeningRightMacroRule {

  /**
   *
   * @param p A proof.
   * @param formulas A list of formulas.
   * @return A new proof whose succedent contains new occurrences of the formulas in formulas.
   */
  def apply( p: LKProof, formulas: Seq[HOLFormula] ): LKProof =
    formulas.foldLeft( p ) { ( acc, x ) => WeakeningRightRule( acc, x ) }

  /**
   *
   * @param p An LKProof.
   * @param formula A Formula.
   * @param n A natural number.
   * @return p extended with weakenings such that formula occurs at least n times in the succedent of the end sequent.
   */
  def apply( p: LKProof, formula: HOLFormula, n: Int ): LKProof = {
    val nCurrent = p.endSequent.succedent.count( _ == formula )

    WeakeningRightMacroRule( p, Seq.fill( n - nCurrent )( formula ) )
  }
}

/**
 * This macro rule simulates a series of weakenings in both cedents.
 *
 */
object WeakeningMacroRule extends RuleConvenienceObject( "WeakeningMacroRule" ) {

  /**
   *
   * @param p A proof.
   * @param antList A list of formulas.
   * @param sucList A list of formulas.
   * @return A new proof whose antecedent and succedent contain new occurrences of the formulas in antList and sucList, respectively.
   */
  def apply( p: LKProof, antList: Seq[HOLFormula], sucList: Seq[HOLFormula] ): LKProof =
    WeakeningRightMacroRule( WeakeningLeftMacroRule( p, antList ), sucList )

  /**
   *
   * @param p A proof.
   * @param targetSequent A sequent of formulas.
   * @param strict If true, will require that targetSequent contains the end sequent of p.
   * @return A proof whose end sequent is targetSequent.
   */
  def apply( p: LKProof, targetSequent: HOLSequent, strict: Boolean = true ): LKProof = {
    val currentSequent = p.endSequent

    if ( strict & !( currentSequent isSubMultisetOf targetSequent ) )
      throw LKRuleCreationException( "Sequent " + targetSequent + " cannot be reached from " + currentSequent + " by weakenings." )

    val ( antDiff, sucDiff ) = ( targetSequent diff currentSequent ).toTuple

    WeakeningMacroRule( p, antDiff, sucDiff )
  }
}

/**
 * This macro rule simulates multiple weakenings and contractions in both cedents.
 *
 */
object WeakeningContractionMacroRule extends RuleConvenienceObject( "WeakeningContractionMacroRule" ) {

  /**
   *
   * @param p An LKProof.
   * @param antList List of pairs (f,n) of type (Formula, Int) that express “f should occur n times in the antecedent”.
   * @param sucList List of pairs (f,n) of type (Formula, Int) that express “f should occur n times in the succedent”.
   * @param strict If true: requires that for (f,n) in antList or sucList, if f occurs in the root of s1, then n > 0.
   * @return
   */
  def apply( p: LKProof, antList: Seq[( HOLFormula, Int )], sucList: Seq[( HOLFormula, Int )], strict: Boolean ): LKProof = {
    val currentAnt = p.endSequent.antecedent
    val currentSuc = p.endSequent.succedent

    val subProof = antList.foldLeft( p )( ( acc, p ) => {
      val ( f, n ) = p
      val nCurrent = currentAnt.count( _ == f )
      if ( n == 0 && nCurrent != 0 && strict )
        throw LKRuleCreationException( "Cannot erase formula occurrences." )

      if ( n > nCurrent )
        WeakeningLeftMacroRule( acc, f, n - nCurrent )
      else if ( n == nCurrent )
        acc
      else // n < nCurrent
        ContractionLeftMacroRule( acc, f, n )
    } )

    sucList.foldLeft( subProof )( ( acc, p ) => {
      val ( f, n ) = p
      val nCurrent = currentSuc.count( _ == f )
      if ( n == 0 && nCurrent != 0 && strict )
        throw LKRuleCreationException( "Cannot erase formula occurrences." )

      if ( n > nCurrent )
        WeakeningRightMacroRule( acc, f, n - nCurrent )
      else if ( n == nCurrent )
        acc
      else // n < nCurrent
        ContractionRightMacroRule( acc, f, n )
    } )
  }

  /**
   *
   * @param p An LKProof.
   * @param targetSequent The proposed end sequent.
   * @param strict If true, will require that the end sequent of p contains no formula that doesn't appear at least once in targetSequent.
   * @return p with its end sequent modified to targetSequent by means of weakening and contraction.
   */
  def apply( p: LKProof, targetSequent: HOLSequent, strict: Boolean = true ): LKProof = {
    val currentSequent = p.endSequent
    val targetAnt = targetSequent.antecedent
    val targetSuc = targetSequent.succedent

    if ( strict && !( currentSequent isSubsetOf targetSequent ) )
      throw LKRuleCreationException( "Sequent " + targetSequent + " cannot be reached from " + currentSequent + " by weakenings and contractions." )

    val antList = targetAnt.distinct map ( f => ( f, targetAnt.count( _ == f ) ) )
    val sucList = targetSuc.distinct map ( f => ( f, targetSuc.count( _ == f ) ) )

    apply( p, antList, sucList, strict )
  }
}

object ParamodulationLeftRule {
  def apply(
    leftSubProof:  LKProof,
    eq:            SequentIndex,
    rightSubProof: LKProof,
    aux:           SequentIndex,
    pos:           HOLPosition
  ): LKProof = {
    val eqFormula = leftSubProof.endSequent( eq )
    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityLeftRule( p1, Ant( 0 ), aux + 1, pos )
    CutRule( leftSubProof, eq, p2, p2.getOccConnector.children( Ant( 0 ) ).head )
  }

  def apply(
    leftSubProof:  LKProof,
    eqFormula:     HOLFormula,
    rightSubProof: LKProof,
    auxFormula:    HOLFormula,
    mainFormula:   HOLFormula
  ): LKProof = {
    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityLeftRule( p1, eqFormula, auxFormula, mainFormula )
    CutRule( leftSubProof, p2, eqFormula )
  }
}

object ParamodulationRightRule {
  def apply(
    leftSubProof:  LKProof,
    eq:            SequentIndex,
    rightSubProof: LKProof,
    aux:           SequentIndex,
    pos:           HOLPosition
  ): LKProof = {
    val eqFormula = leftSubProof.endSequent( eq )
    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityRightRule( p1, Ant( 0 ), aux, pos )
    CutRule( leftSubProof, eq, p2, p2.getOccConnector.children( Ant( 0 ) ).head )
  }

  def apply(
    leftSubProof:  LKProof,
    eqFormula:     HOLFormula,
    rightSubProof: LKProof,
    auxFormula:    HOLFormula,
    mainFormula:   HOLFormula
  ): LKProof = {
    val p1 = WeakeningLeftRule( rightSubProof, eqFormula )
    val p2 = EqualityRightRule( p1, eqFormula, auxFormula, mainFormula )
    CutRule( leftSubProof, p2, eqFormula )
  }
}

/**
 * Move a formula to the beginning of the antecedent, where the main formula is customarily placed.
 * <pre>
 *          (π)
 *     Γ, A, Γ' :- Δ
 *    --------------
 *     A, Γ, Γ' :- Δ
 * </pre>
 */
object ExchangeLeftMacroRule {
  def apply( subProof: LKProof, aux: SequentIndex ) = {
    require( aux isAnt )
    require( subProof.endSequent isDefinedAt aux )
    ContractionLeftRule( WeakeningLeftRule( subProof, subProof.endSequent( aux ) ), Ant( 0 ), aux + 1 )
  }
}

/**
 * Move a formula to the end of the succedent, where the main formula is customarily placed.
 * <pre>
 *          (π)
 *     Γ :- Δ, A, Δ'
 *    --------------
 *     Γ :- Δ, Δ', A
 * </pre>
 */
object ExchangeRightMacroRule {
  def apply( subProof: LKProof, aux: SequentIndex ) = {
    require( aux isSuc )
    require( subProof.endSequent isDefinedAt aux )
    ContractionRightRule( WeakeningRightRule( subProof, subProof.endSequent( aux ) ), aux, Suc( subProof.endSequent.succedent.size ) )
  }
}

/**
 * Computes a proof of F from a proof of some instances of F
 *
 */
object proofFromInstances {
  /**
   *
   * @param s1 An LKProof containing the instances in es in its end sequent.
   * @param es An ExpansionSequent in which all shallow formulas are prenex and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep sequent of es.
   */
  def apply( s1: LKProof, es: ExpansionSequent ): LKProof =
    ( es.antecedent ++ es.succedent ).foldLeft( s1 )( apply )

  /**
   *
   * @param s1 An LKProof containing the instances in et in its end sequent
   * @param et An ExpansionTree whose shallow formula is prenex and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep formula of et.
   */
  def apply( s1: LKProof, et: ExpansionTree ): LKProof = apply( s1, compressQuantifiers( et ) )

  /**
   *
   * @param s1 An LKProof containing the instances in mes in its end sequent.
   * @param mes A MultiExpansionSequent in which all shallow formulas are prenex and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep sequent of mes.
   */
  def apply( s1: LKProof, mes: MultiExpansionSequent )( implicit dummyImplicit: DummyImplicit ): LKProof = ( mes.antecedent ++ mes.succedent ).foldLeft( s1 )( apply )

  /**
   *
   * @param s1 An LKProof containing the instances in et in its end sequent
   * @param met A MultiExpansionTree whose shallow formula is prenex and which contains no strong or Skolem quantifiers.
   * @return A proof starting with s1 and ending with the deep formula of met.
   */
  def apply( s1: LKProof, met: MultiExpansionTree ): LKProof = {
    require( isPrenex( met.toShallow ), "Shallow formula of " + met + " is not prenex" )

    met match {
      case METWeakQuantifier( f @ All( _, _ ), instances ) =>
        val tmp = instances.foldLeft( s1 ) {
          ( acc, i ) => ForallLeftBlock( acc, f, i._2 )
        }

        ContractionLeftMacroRule( tmp, f )

      case METWeakQuantifier( f @ Ex( _, _ ), instances ) =>
        val tmp = instances.foldLeft( s1 ) {
          ( acc, i ) => ExistsRightBlock( acc, f, i._2 )
        }

        ContractionRightMacroRule( tmp, f )

      case METSkolemQuantifier( _, _, _ ) | METStrongQuantifier( _, _, _ ) =>
        throw new UnsupportedOperationException( "This case is not handled at this time." )
      case _ => s1
    }
  }
}
