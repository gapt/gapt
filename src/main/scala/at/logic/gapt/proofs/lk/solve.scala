package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.resolution.RobinsonToLK
import at.logic.gapt.provers.{ ResolutionProver, OneShotProver, Prover }
import at.logic.gapt.utils.logging.Logger

/**
 * Bottom-up construction of sequent calculus proofs.
 *
 * Currently supports propositional logic as well as proof construction using expansion trees.
 */
object solve extends Logger {
  /**
   * Main method for solving propositional sequents
   *
   * @param seq: sequent to prove
   * @return a proof if there is one
   */
  def solvePropositional( seq: HOLSequent ): Option[LKProof] =
    startProving( seq, new PropositionalProofStrategy, _ => None )

  def solvePropositional( formula: HOLFormula ): Option[LKProof] =
    solvePropositional( Sequent() :+ formula )

  /**
   * Transform expansion proof to LK proof (assumes that deep formula of expansionSequent is a tautology)
   */
  def expansionProofToLKProof( expansionSequent: ExpansionSequent, qfProver: Option[ResolutionProver] = None ): Option[LKProof] =
    startProving( toShallow( expansionSequent ), new ExpansionTreeProofStrategy( expansionSequent ),
      qfProver match {
        case Some( prover ) =>
          seq => prover getRobinsonProof seq.filter { isAtom( _ ) } map { ref =>
            RobinsonToLK( ref, Sequent(), cls => LogicalAxiom( cls.elements.head ), addWeakenings = false )
          }
        case None => _ => None
      } )

  // internal interface method
  private def startProving( seq: HOLSequent, strategy: ProofStrategy, fallback: HOLSequent => Option[LKProof] ): Option[LKProof] =
    prove( seq.distinct, strategy, fallback ) map { WeakeningMacroRule( _, seq ) }

  private def prove( seq: HOLSequent, strategy: ProofStrategy, fallback: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    // we are only proving set-normalized sequents
    val antSet = seq.antecedent.toSet
    val sucSet = seq.succedent.toSet
    assert( antSet.size == seq.antecedent.size && sucSet.size == seq.succedent.size )

    trace( "proving: " + seq )
    trace( "with strat: " + strategy )

    if ( seq.isTaut ) {
      Some( LogicalAxiom( seq.antecedent intersect seq.succedent head ) )
    } else {

      trace( "no axiom, calc next step" )

      // main step: ask strategy what to do
      strategy.calcNextStep( seq ) match {
        case Some( action ) =>
          trace( "strategy has selected: " + action + " action.form: " + action.formula )

          // apply whatever rule matches to this formula
          action.loc match {
            case ProofStrategy.FormulaLocation.Antecedent =>
              assert( seq.antecedent.contains( action.formula ) )
              applyActionAntecedent( action, seq, fallback )

            case ProofStrategy.FormulaLocation.Succedent =>
              assert( seq.succedent.contains( action.formula ) )
              applyActionSuccedent( action, seq, fallback )
          }

        case None => fallback( seq )
      }
    }
  }

  private def applyActionAntecedent( action: ProofStrategy.Action, seq: HOLSequent, fallback: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    // sequent without principal formula to help building upper goal sequent
    val rest = HOLSequent( seq.antecedent.diff( action.formula :: Nil ), seq.succedent )
    // proof strategies for children (with expansion sequents according to children or no changes in the propositional case)
    val nextProofStrategies = action.getNextStrategies

    val rv = action.formula match {

      // Quantifier Rules

      case All( v, f ) => {
        val quantifiedTerm = action.getQuantifiedTerm.get // must be defined in this case
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, quantifiedTerm )( f ) )

        val p_ant = if ( seq.antecedent.contains( auxFormula ) ) seq.antecedent else auxFormula +: seq.antecedent
        val p_suc = seq.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof => {
          if ( proof.endSequent.antecedent.contains( auxFormula ) && !rest.antecedent.contains( auxFormula ) ) {
            val proof1 = ForallLeftRule( proof, action.formula, quantifiedTerm )
            if ( proof.endSequent.antecedent.contains( action.formula ) ) // main formula already appears in upper proof
              ContractionLeftRule( proof1, action.formula )
            else
              proof1
          } else
            proof
        } )
      }

      case Ex( v, f ) => {
        val eigenVar = action.getQuantifiedTerm.get.asInstanceOf[Var]
        val auxFormula = Substitution( v, eigenVar )( f )

        val p_ant = if ( seq.antecedent.contains( auxFormula ) ) rest.antecedent else auxFormula +: rest.antecedent
        val p_suc = seq.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.antecedent.contains( auxFormula ) && !rest.antecedent.contains( auxFormula ) )
            ExistsLeftRule( proof, action.formula, eigenVar )
          else
            proof )
      }

      // Nullary rules
      case Bottom() => Some( WeakeningMacroRule( BottomAxiom, seq ) )

      // Unary Rules

      case Neg( f1 ) => {
        val p_ant = rest.antecedent
        val p_suc = if ( seq.succedent.contains( f1 ) ) seq.succedent else f1 +: rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.succedent.contains( f1 ) && !rest.succedent.contains( f1 ) )
            NegLeftRule( proof, f1 )
          else
            proof )
      }

      case And( f1, f2 ) => {
        val f1_opt = if ( rest.antecedent.contains( f1 ) ) Nil else f1 :: Nil
        val f2_opt = if ( ( f1_opt ++ rest.antecedent ).contains( f2 ) ) Nil else f2 :: Nil
        val p_ant = f1_opt ++ f2_opt ++ rest.antecedent
        val p_suc = rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.antecedent.contains( f1 ) || proof.endSequent.antecedent.contains( f2 ) )
            AndLeftMacroRule( proof, f1, f2 )
          else
            proof )
      }

      // Binary Rules

      case Or( f1, f2 ) => {
        val p_ant1 = if ( rest.antecedent.contains( f1 ) ) rest.antecedent else f1 +: rest.antecedent
        val p_suc1 = rest.succedent
        val premise1 = HOLSequent( p_ant1, p_suc1 )

        prove( premise1, nextProofStrategies( 0 ), fallback ) match {
          case Some( proof1 ) =>
            if ( proof1.endSequent.antecedent.contains( f1 ) && !rest.antecedent.contains( f1 ) ) {
              val p_ant2 = if ( rest.antecedent.contains( f2 ) ) rest.antecedent else f2 +: rest.antecedent
              val p_suc2 = rest.succedent
              val premise2 = HOLSequent( p_ant2, p_suc2 )

              prove( premise2, nextProofStrategies( 1 ), fallback ).map( proof2 =>
                if ( proof2.endSequent.antecedent.contains( f2 ) && !rest.antecedent.contains( f2 ) )
                  ContractionMacroRule( OrLeftRule( proof1, f1, proof2, f2 ) )
                else
                  proof2 )
            } else {
              Some( proof1 )
            }
          case None => None
        }
      }

      case Imp( f1, f2 ) => {
        val p_ant1 = rest.antecedent
        val p_suc1 = if ( rest.succedent.contains( f1 ) ) rest.succedent else f1 +: rest.succedent
        val premise1 = HOLSequent( p_ant1, p_suc1 )

        prove( premise1, nextProofStrategies( 0 ), fallback ) match {
          case Some( proof1 ) =>
            if ( proof1.endSequent.succedent.contains( f1 ) && !rest.succedent.contains( f1 ) ) {
              val p_ant2 = if ( rest.antecedent.contains( f2 ) ) rest.antecedent else f2 +: rest.antecedent
              val p_suc2 = rest.succedent
              val premise2 = HOLSequent( p_ant2, p_suc2 )

              prove( premise2, nextProofStrategies( 1 ), fallback ).map( proof2 =>
                if ( proof2.endSequent.antecedent.contains( f2 ) && !rest.antecedent.contains( f2 ) )
                  ContractionMacroRule( ImpLeftRule( proof1, f1, proof2, f2 ) )
                else
                  proof2 )
            } else {
              Some( proof1 )
            }
          case None => None
        }
      }
    }

    // invariant: we have constructed a proof of a subsequent of seq
    if ( rv.isDefined ) assert( rv.get.endSequent.isSubsetOf( seq ) )

    rv
  }

  private def applyActionSuccedent( action: ProofStrategy.Action, seq: HOLSequent, fallback: HOLSequent => Option[LKProof] ): Option[LKProof] = {
    val rest = HOLSequent( seq.antecedent, seq.succedent.diff( action.formula :: Nil ) )
    val nextProofStrategies = action.getNextStrategies

    val rv = action.formula match {

      // Quantifier Rules

      case All( v, f ) => {
        val eigenVar = action.getQuantifiedTerm.get.asInstanceOf[Var]
        val auxFormula = Substitution( v, eigenVar )( f )

        val p_ant = rest.antecedent
        val p_suc = if ( rest.succedent.contains( auxFormula ) ) rest.succedent else auxFormula +: rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.succedent.contains( auxFormula ) && !rest.succedent.contains( auxFormula ) )
            ForallRightRule( proof, action.formula, eigenVar )
          else
            proof )
      }

      case Ex( v, f ) => {
        val quantifiedTerm = action.getQuantifiedTerm.get
        val auxFormula = BetaReduction.betaNormalize( Substitution( v, quantifiedTerm )( f ) )

        val p_ant = rest.antecedent
        val p_suc = if ( seq.succedent.contains( auxFormula ) ) seq.succedent else auxFormula +: seq.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof => {
          if ( proof.endSequent.succedent.contains( auxFormula ) && !rest.succedent.contains( auxFormula ) ) {
            val proof1 = ExistsRightRule( proof, action.formula, quantifiedTerm )
            if ( proof.endSequent.succedent.contains( action.formula ) )
              ContractionRightRule( proof1, action.formula )
            else
              proof1
          } else
            proof
        } )
      }

      // Nullary rules
      case Top() => Some( WeakeningMacroRule( TopAxiom, seq ) )

      // Unary Rules

      case Neg( f1 ) => {
        val p_ant = if ( rest.antecedent.contains( f1 ) ) rest.antecedent else f1 +: rest.antecedent
        val p_suc = rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.antecedent.contains( f1 ) && !rest.antecedent.contains( f1 ) )
            NegRightRule( proof, f1 )
          else
            proof )
      }

      case Imp( f1, f2 ) => {
        val p_ant = if ( rest.antecedent.contains( f1 ) ) rest.antecedent else f1 +: rest.antecedent
        val p_suc = if ( rest.succedent.contains( f2 ) ) rest.succedent else f2 +: rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof => {
          val infer_on_f1 = proof.endSequent.antecedent.contains( f1 ) && !rest.antecedent.contains( f1 )
          val infer_on_f2 = proof.endSequent.succedent.contains( f2 ) && !rest.succedent.contains( f2 )

          if ( infer_on_f1 || infer_on_f2 ) { // need to infer main formula
            val proof1 = if ( !infer_on_f1 ) WeakeningLeftRule( proof, f1 ) else proof
            val proof2 = if ( !infer_on_f2 ) WeakeningRightRule( proof1, f2 ) else proof1
            ImpRightRule( proof2, f1, f2 )
          } else {
            proof
          }
        } )
      }

      case Or( f1, f2 ) => {
        val f1_opt = if ( rest.succedent.contains( f1 ) ) Nil else f1 :: Nil
        val f2_opt = if ( ( f1_opt ++ rest.succedent ).contains( f2 ) ) Nil else f2 :: Nil
        val p_ant = rest.antecedent
        val p_suc = f1_opt ++ f2_opt ++ rest.succedent
        val premise = HOLSequent( p_ant, p_suc )

        prove( premise, nextProofStrategies( 0 ), fallback ).map( proof =>
          if ( proof.endSequent.succedent.contains( f1 ) || proof.endSequent.succedent.contains( f2 ) )
            OrRightMacroRule( proof, f1, f2 )
          else
            proof )
      }

      // Binary Rules

      case And( f1, f2 ) => {
        val p_ant1 = rest.antecedent
        val p_suc1 = if ( rest.succedent.contains( f1 ) ) rest.succedent else f1 +: rest.succedent
        val premise1 = HOLSequent( p_ant1, p_suc1 )

        prove( premise1, nextProofStrategies( 0 ), fallback ) match {
          case Some( proof1 ) =>
            if ( proof1.endSequent.succedent.contains( f1 ) && !rest.succedent.contains( f1 ) ) {
              val p_ant2 = rest.antecedent
              val p_suc2 = if ( rest.succedent.contains( f2 ) ) rest.succedent else f2 +: rest.succedent
              val premise2 = HOLSequent( p_ant2, p_suc2 )

              prove( premise2, nextProofStrategies( 1 ), fallback ).map( proof2 =>
                if ( proof2.endSequent.succedent.contains( f2 ) && !rest.succedent.contains( f2 ) )
                  ContractionMacroRule( AndRightRule( proof1, f1, proof2, f2 ) )
                else
                  proof2 )
            } else {
              Some( proof1 )
            }
          case None => None
        }
      }

    }

    // invariant: we have constructed a proof of a subsequent of seq
    if ( rv.isDefined ) assert( rv.get.endSequent.isSubsetOf( seq ) )

    rv
  }
}

/**
 * Strategy to tell prove procedure which rules to apply
 *
 * A strategy selects a next action to execute. An action is represented by
 * a formula and the information whether this formula is in the antecedent
 * or the succedent. The action is to apply a rule to this formula.
 */
abstract class ProofStrategy {
  def calcNextStep( seq: HOLSequent ): Option[ProofStrategy.Action]
}
object ProofStrategy {
  object FormulaLocation extends Enumeration { val Succedent, Antecedent = Value }

  class Action( val formula: HOLFormula, val loc: FormulaLocation.Value, private val oldStrategy: Option[ProofStrategy] ) {
    override def toString = "ProofStrategy.Action(" + formula + ", " + loc + ")"

    /**
     * Returns strategy to use for proving children
     */
    def getNextStrategies: Seq[ProofStrategy] = {
      formula match { // either one or two branches
        case ( Or( _, _ ) | Imp( _, _ ) ) if loc == FormulaLocation.Antecedent => List( oldStrategy.get, oldStrategy.get )
        case ( And( _, _ ) ) if loc == FormulaLocation.Succedent => List( oldStrategy.get, oldStrategy.get )
        case _ => List( oldStrategy.get )
      }
    }

    def getQuantifiedTerm: Option[LambdaExpression] = None
  }
}

/**
 * Strategy for proving propositional sequents.
 */
class PropositionalProofStrategy extends ProofStrategy with Logger {
  val FormulaLocation = ProofStrategy.FormulaLocation // shortcut

  override def calcNextStep( seq: HOLSequent ): Option[ProofStrategy.Action] = {

    // rule preference:
    None.
      orElse( findNullaryLeft( seq ) ).
      orElse( findNullaryRight( seq ) ).
      orElse( findUnaryLeft( seq ) ).
      orElse( findUnaryRight( seq ) ).
      orElse( findBinaryLeft( seq ) ).
      orElse( findBinaryRight( seq ) ).
      orElse {
        debug( "PropositionalProofStrategy is unable to find a rule to apply on: " + seq )
        None
      }
  }

  def findNullaryLeft( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.antecedent.find( {
      case Bottom() => true
      case _        => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Antecedent, Some( this ) ) )
  def findNullaryRight( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.succedent.find( {
      case Top() => true
      case _     => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Succedent, Some( this ) ) )

  // Tries to find a formula on the left or on the right such that its
  // introduction rule is unary.
  def findUnaryLeft( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.antecedent.find( {
      case Neg( _ ) | And( _, _ ) => true
      case _                      => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Antecedent, Some( this ) ) )
  def findUnaryRight( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.succedent.find( {
      case Neg( _ ) | Imp( _, _ ) | Or( _, _ ) => true
      case _                                   => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Succedent, Some( this ) ) )

  // Tries to find a formula on the left or on the right such that its
  // introduction rule is binary.
  def findBinaryLeft( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.antecedent.find( {
      case Imp( _, _ ) | Or( _, _ ) => true
      case _                        => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Antecedent, Some( this ) ) )
  def findBinaryRight( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.succedent.find( {
      case And( _, _ ) => true
      case _           => false
    } ).map( new ProofStrategy.Action( _, FormulaLocation.Succedent, Some( this ) ) )

}

/**
 * Strategy for constructing a proof from an ExpansionSequent.
 *
 * The internal state of this strategy is an ExpansionSequent. The action is
 * a formula on a side of the sequent plus a witness term or eigenvariable
 * respectively in case this formula starts with a quantifier.
 */
class ExpansionTreeProofStrategy( val expansionSequent: ExpansionSequent ) extends PropositionalProofStrategy with at.logic.gapt.utils.logging.Logger {

  override def toString: String = "ExpansionTreeProofStrategy(" + expansionSequent + ")"

  override def calcNextStep( seq: HOLSequent ): Option[ProofStrategy.Action] = {
    // every possible action (i.e. formula in toShallow( expansionSequent )) must be realizable (in seq)
    assert( toShallow( expansionSequent ).isSubsetOf( seq ) )

    val goal_pruned = removeWeakFormulas( seq )

    // rule preference:
    None.
      orElse( findNullaryLeft( goal_pruned ) ).
      orElse( findNullaryRight( goal_pruned ) ).
      orElse( findUnaryLeft( goal_pruned ) ).
      orElse( findUnaryRight( goal_pruned ) ).
      orElse( findStrongQuantifier( goal_pruned ) ). // can always apply strong quantifier
      orElse( findWeakQuantifier( goal_pruned ) ). // weak before binary rules since it's unary
      orElse( findBinaryLeft( goal_pruned ) ).
      orElse( findBinaryRight( goal_pruned ) ).
      orElse {
        debug( "ExpansionTreeProofStrategy is unable to find a rule to apply on: " + seq )
        None
      }
  }

  /**
   * Remove all formulas from seq which correspond to top-level ETWeakening-nodes in expansionSequent
   *
   * This assumes that Shallow( expansionSequent ) is a subset of seq and that there are no duplicate
   * formulas in seq.
   */
  private def removeWeakFormulas( seq: HOLSequent ) = {
    val w_ant = expansionSequent.antecedent.filter( {
      case ETWeakening( _, _ ) => true
      case _                   => false
    } ).map( toShallow( _ ) )
    val w_suc = expansionSequent.succedent.filter( {
      case ETWeakening( _, _ ) => true
      case _                   => false
    } ).map( toShallow( _ ) )

    HOLSequent( seq.antecedent.filterNot( w_ant.contains( _ ) ), seq.succedent.filterNot( w_suc.contains( _ ) ) )
  }

  // TODO:  why do find... operate on seq, would it not make more sense to have them work on expansionSequent?
  //        in particular since we have assert( toShallow( expansionSequent ).isSubsetOf( seq ) )

  /**
   * need to override find-methods as we keep track of the state of the expansion sequent here
   */
  override def findUnaryLeft( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.antecedent.find( {
      case Neg( _ ) | And( _, _ ) => true
      case _                      => false
    } ).map( formula => formula match {
      case Neg( f1 ) =>
        trace( "found neg left; exp seq: " + expansionSequent + "; formula: " + formula )
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = true ).get
        val etSeq1 = expansionSequent.removeFromAntecedent( et ) :+ et.immediateSubProofs( 0 )
        val ps1 = new ExpansionTreeProofStrategy( etSeq1 )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Antecedent, None, List[ProofStrategy]( ps1 ) )
      case And( f1, f2 ) =>
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = true ).get
        val etSeq =
          et.immediateSubProofs( 1 ) +:
            et.immediateSubProofs( 0 ) +:
            expansionSequent.removeFromAntecedent( et )
        val ps1 = new ExpansionTreeProofStrategy( etSeq )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Antecedent, None, List[ProofStrategy]( ps1 ) )
    } )

  override def findUnaryRight( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.succedent.find( {
      case Neg( _ ) | Imp( _, _ ) | Or( _, _ ) => true
      case _                                   => false
    } ).map( formula => formula match {
      case Neg( f1 ) =>
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = false ).get
        val etSeq1 = et.immediateSubProofs( 0 ) +: expansionSequent.removeFromSuccedent( et )
        val ps1 = new ExpansionTreeProofStrategy( etSeq1 )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Succedent, None, List[ProofStrategy]( ps1 ) )
      case Imp( f1, f2 ) =>
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = false ).get
        val etSeq =
          et.immediateSubProofs( 0 ) +:
            expansionSequent
            .replaceInSuccedent( et, et.immediateSubProofs( 1 ) )
            .asInstanceOf[ExpansionSequent]
        val ps1 = new ExpansionTreeProofStrategy( etSeq )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Succedent, None, List[ProofStrategy]( ps1 ) )
      case Or( f1, f2 ) =>
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = false ).get
        val etSeq = ( expansionSequent
          .replaceInSuccedent( et, et.immediateSubProofs( 1 ) )
          :+ et.immediateSubProofs( 0 ) )
          .asInstanceOf[ExpansionSequent]
        val ps1 = new ExpansionTreeProofStrategy( etSeq )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Succedent, None, List[ProofStrategy]( ps1 ) )
    } )

  override def findBinaryRight( seq: HOLSequent ): Option[ProofStrategy.Action] =
    seq.succedent.find( {
      case And( _, _ ) => true
      case _           => false
    } ).map( formula => {
      // prepare new proof strategies for children
      val et = getETOfFormula( expansionSequent, formula, isAntecedent = false ).get
      val etSeq1 = expansionSequent.replaceInSuccedent( et, et.immediateSubProofs( 0 ) )
      val etSeq2 = expansionSequent.replaceInSuccedent( et, et.immediateSubProofs( 1 ) )
      val ps1 = new ExpansionTreeProofStrategy( etSeq1 )
      val ps2 = new ExpansionTreeProofStrategy( etSeq2 )
      new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Succedent, None, List[ProofStrategy]( ps1, ps2 ) )
    } )

  override def findBinaryLeft( seq: HOLSequent ): Option[ProofStrategy.Action] = {
    seq.antecedent.find( {
      case Imp( _, _ ) | Or( _, _ ) => true
      case _                        => false
    } ).map( formula => formula match {
      // differentiate again between Imp and Or as formulas appear in different locations when proving
      case Imp( _, _ ) => {
        trace( "found imp left; exp seq: " + expansionSequent + "; formula: " + formula )
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = true ).get
        val children = et.immediateSubProofs // children are Tuple2(ET, Option[Formula])
        val etSeqPurged = expansionSequent.removeFromAntecedent( et )
        val etSeq1 = new ExpansionSequent( etSeqPurged.antecedent, children( 0 ) +: etSeqPurged.succedent )
        val etSeq2 = new ExpansionSequent( children( 1 ) +: etSeqPurged.antecedent, etSeqPurged.succedent )
        val ps1 = new ExpansionTreeProofStrategy( etSeq1 )
        val ps2 = new ExpansionTreeProofStrategy( etSeq2 )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Antecedent, None, List[ProofStrategy]( ps1, ps2 ) )
      }
      case Or( _, _ ) => {
        val et = getETOfFormula( expansionSequent, formula, isAntecedent = true ).get
        val etSeq1 = expansionSequent.replaceInAntecedent( et, et.immediateSubProofs( 0 ) )
        val etSeq2 = expansionSequent.replaceInAntecedent( et, et.immediateSubProofs( 1 ) )
        val ps1 = new ExpansionTreeProofStrategy( etSeq1 )
        val ps2 = new ExpansionTreeProofStrategy( etSeq2 )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( formula, FormulaLocation.Antecedent, None, List[ProofStrategy]( ps1, ps2 ) )
      }
    } )
  }

  def findStrongQuantifier( seq: HOLSequent ): Option[ExpansionTreeProofStrategy.ExpansionTreeAction] = {
    // find one instance, can just use it
    // return etseq (in strategy) with formula removed, but keep instance

    val anteResult = expansionSequent.antecedent.collectFirst( {
      case et @ ETStrongQuantifier( formula, variable, selection ) =>
        val newEtSeq = expansionSequent.replaceInAntecedent( et, selection )
        new ExpansionTreeProofStrategy.ExpansionTreeAction( toShallow( et ), FormulaLocation.Antecedent, Some( variable ),
          List( new ExpansionTreeProofStrategy( newEtSeq ) ) )
    } )

    anteResult.orElse(
      expansionSequent.succedent.collectFirst( {
        case et @ ETStrongQuantifier( formula, variable, selection ) =>
          val newEtSeq = expansionSequent.replaceInSuccedent( et, selection )
          new ExpansionTreeProofStrategy.ExpansionTreeAction( toShallow( et ), FormulaLocation.Succedent, Some( variable ),
            List( new ExpansionTreeProofStrategy( newEtSeq ) ) )
      } )
    )
  }

  /**
   * Check if *any* of vars appears as strong quantifier somewhere in et
   * Naive approach: always check everything.
   * This data does not really change (except on et seq changes), so it could be cached/precalculated for efficiency in the future
   */
  private def doVariablesAppearInStrongQuantifier( vars: Set[Var], et: ExpansionTree ): Boolean =
    et.subProofs exists {
      case ETStrongQuantifier( _, ev, _ ) if vars contains ev => true
      case _ => false
    }

  def findWeakQuantifier( seq: HOLSequent ): Option[ExpansionTreeProofStrategy.ExpansionTreeAction] = {
    // check which of the terms to use (just ones that aren't there yet)
    // return etseq (in strat) with instance removed
    // -> check for:
    // any of set of variables of term used as expansion term in weak quantifier expansion is used as strong quantifier elsewhere (and hasn't been reduced so far, i.e. appears in current expansion sequent)
    // also in cyclicity condition: expand outer instantiations before inner (can't magically make inner part of formula appear, only rule by rule). this is done automatically if only outermost occurences of weak
    // quantifier instances are checked here

    def getFirstApplicableInstanceOfWeakQuantifier( instances: Map[LambdaExpression, ExpansionTree] ) =
      instances.find {
        case ( term, et ) =>
          // check if free variables of term appear in any strong quantifier
          eigenVariablesET( expansionSequent ).intersect( freeVariables( term ) ).isEmpty
      }

    val anteResult: Option[ExpansionTreeProofStrategy.ExpansionTreeAction] = expansionSequent.antecedent.foldLeft( None: Option[ExpansionTreeProofStrategy.ExpansionTreeAction] )( ( old, et ) =>
      // want to return first match, so return old if defined or check next
      old.orElse( {
        et match {
          case ETWeakQuantifier( formula, instances ) =>
            getFirstApplicableInstanceOfWeakQuantifier( instances ).map( instancePicked => {
              val newInstances = instances.filterNot( _ == instancePicked )
              // drop et as soon as all instances have been picked (from etseq, will stick in actual sequent for simplicity but never be chosen)
              val newEtSeq0 =
                if ( newInstances.isEmpty ) { expansionSequent.removeFromAntecedent( et ) }
                else { expansionSequent.replaceInAntecedent( et, ETWeakQuantifier( formula, newInstances ) ) }
              val newEtSeq = instancePicked._2 +: newEtSeq0
              new ExpansionTreeProofStrategy.ExpansionTreeAction( toShallow( et ), FormulaLocation.Antecedent, Some( instancePicked._1 ),
                List( new ExpansionTreeProofStrategy( newEtSeq ) ) )
            } )
          case _ => None
        }
      } ) )

    if ( anteResult.isDefined ) { // this should be anteResult.getOrElse (as anywhere else), but the scala compiler tries really hard to prevent this, so who am i to force it..
      anteResult
    } else {
      val succResult: Option[ExpansionTreeProofStrategy.ExpansionTreeAction] =
        expansionSequent.succedent.foldLeft( None: Option[ExpansionTreeProofStrategy.ExpansionTreeAction] )( ( old, et ) =>
          // want to return first match, so return old if defined or check next
          old.orElse( {
            et match {
              case ETWeakQuantifier( formula, instances ) =>
                getFirstApplicableInstanceOfWeakQuantifier( instances ).map( instancePicked => {
                  val newInstances = instances.filterNot( _ == instancePicked )
                  // drop et as soon as all instances have been picked
                  val newEtSeq0 =
                    if ( newInstances.isEmpty ) { expansionSequent.removeFromSuccedent( et ) }
                    else { expansionSequent.replaceInSuccedent( et, ETWeakQuantifier( formula, newInstances ) ) }
                  val newEtSeq = newEtSeq0 :+ instancePicked._2
                  new ExpansionTreeProofStrategy.ExpansionTreeAction( toShallow( et ), FormulaLocation.Succedent, Some( instancePicked._1 ),
                    List( new ExpansionTreeProofStrategy( newEtSeq ) ) )
                } )
              case _ => None
            }
          } ) )
      succResult
    }
  }
}

object ExpansionTreeProofStrategy {
  class ExpansionTreeAction( override val formula: HOLFormula, override val loc: ProofStrategy.FormulaLocation.Value,
                             val quantifiedTerm: Option[LambdaExpression], val subStrategy: Seq[ProofStrategy] )
      extends ProofStrategy.Action( formula, loc, None ) {
    override def toString = "ExpansionTreeAction(" + formula + ", " + loc + ", " + quantifiedTerm + "," + subStrategy + ")"
    override def getNextStrategies: Seq[ProofStrategy] = subStrategy
    override def getQuantifiedTerm: Option[LambdaExpression] = quantifiedTerm
  }
}

/**
 * Gets expansion tree of a formula from expansion sequent.
 */
private object getETOfFormula {
  def apply( etSeq: ExpansionSequent, f: HOLFormula, isAntecedent: Boolean ): Option[ExpansionTree] = {
    getFromExpansionTreeList( if ( isAntecedent ) etSeq.antecedent else etSeq.succedent, f )
  }

  private def getFromExpansionTreeList( ets: Seq[ExpansionTree], f: HOLFormula ): Option[ExpansionTree] = ets match {
    case head +: tail =>
      if ( toShallow( head ) == f ) Some( head )
      else getFromExpansionTreeList( tail, f )
    case Seq() => None
  }
}

object LKProver extends OneShotProver {
  def getLKProof( seq: HOLSequent ): Option[LKProof] = solve.solvePropositional( seq )
}

object AtomicExpansion {

  def apply( fs: HOLSequent ): LKProof =
    WeakeningMacroRule( apply( fs.antecedent intersect fs.succedent head ), fs )

  def apply( f: HOLFormula ): LKProof = f match {
    case a: HOLAtom  => LogicalAxiom( a )

    case Bottom()    => WeakeningRightRule( BottomAxiom, Bottom() )
    case Top()       => WeakeningLeftRule( TopAxiom, Top() )

    case Neg( l )    => NegLeftRule( NegRightRule( apply( l ), Ant( 0 ) ), Suc( 0 ) )

    case And( l, r ) => AndLeftRule( AndRightRule( apply( l ), Suc( 0 ), apply( r ), Suc( 0 ) ), Ant( 0 ), Ant( 1 ) )
    case Or( l, r )  => OrRightRule( OrLeftRule( apply( l ), Ant( 0 ), apply( r ), Ant( 0 ) ), Suc( 0 ), Suc( 1 ) )
    case Imp( l, r ) => ImpRightRule( ImpLeftRule( apply( l ), Suc( 0 ), apply( r ), Ant( 0 ) ), Ant( 1 ), Suc( 0 ) )

    case All( x, l ) => ForallRightRule( ForallLeftRule( apply( l ), Ant( 0 ), l, x, x ), Suc( 0 ), x, x )
    case Ex( x, l )  => ExistsLeftRule( ExistsRightRule( apply( l ), Suc( 0 ), l, x, x ), Ant( 0 ), x, x )
  }

  def apply( p: LKProof ): LKProof = p match {
    case ReflexivityAxiom( _ ) | TopAxiom | BottomAxiom | TheoryAxiom( _ ) => p
    case LogicalAxiom( f ) => apply( f )

    //structural rules
    case ContractionLeftRule( subProof, aux1, aux2 ) => ContractionLeftRule( apply( subProof ), aux1, aux2 )
    case ContractionRightRule( subProof, aux1, aux2 ) => ContractionRightRule( apply( subProof ), aux1, aux2 )

    case WeakeningLeftRule( subProof, main ) => WeakeningLeftRule( apply( subProof ), main )
    case WeakeningRightRule( subProof, main ) => WeakeningRightRule( apply( subProof ), main )

    case CutRule( subProof1, aux1, subProof2, aux2 ) => CutRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )

    //Unary Logical rules
    case NegLeftRule( subProof, aux ) => NegLeftRule( apply( subProof ), aux )
    case NegRightRule( subProof, aux ) => NegRightRule( apply( subProof ), aux )

    case ImpRightRule( subProof, aux1, aux2 ) => ImpRightRule( apply( subProof ), aux1, aux2 )
    case OrRightRule( subProof, aux1, aux2 ) => OrRightRule( apply( subProof ), aux1, aux2 )
    case AndLeftRule( subProof, aux1, aux2 ) => AndLeftRule( apply( subProof ), aux1, aux2 )

    //Binary Logical Rules
    case ImpLeftRule( subProof1, aux1, subProof2, aux2 ) => ImpLeftRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )
    case OrLeftRule( subProof1, aux1, subProof2, aux2 ) => OrLeftRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )
    case AndRightRule( subProof1, aux1, subProof2, aux2 ) => AndRightRule( apply( subProof1 ), aux1, apply( subProof2 ), aux2 )

    //Quantifier Rules
    case ForallLeftRule( subProof, aux, formula, term, v ) => ForallLeftRule( apply( subProof ), aux, formula, term, v )
    case ExistsRightRule( subProof, aux, formula, term, v ) => ExistsRightRule( apply( subProof ), aux, formula, term, v )

    case ForallRightRule( subProof, aux, eigen, quant ) => ForallRightRule( apply( subProof ), aux, eigen, quant )
    case ExistsLeftRule( subProof, aux, eigen, quant ) => ExistsLeftRule( apply( subProof ), aux, eigen, quant )

    //equality and definitions
    case EqualityLeftRule( subProof, eq, aux, pos ) => EqualityLeftRule( apply( subProof ), eq, aux, pos )
    case EqualityRightRule( subProof, eq, aux, pos ) => EqualityRightRule( apply( subProof ), eq, aux, pos )

    case DefinitionLeftRule( subProof, aux, main ) => DefinitionLeftRule( apply( subProof ), aux, main )
    case DefinitionRightRule( subProof, aux, main ) => DefinitionRightRule( apply( subProof ), aux, main )
  }

}
