/**
 * Cut introduction algorithm
 *
 *
 */
package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.cutIntroduction.Deltas._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.calculi.expansionTrees.{ quantRulesNumber => quantRulesNumberET, toFSequent, ExpansionSequent }
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.language.fol._
import at.logic.language.hol.HOLFormula
import at.logic.provers.basicProver._
import at.logic.provers.eqProver._
import at.logic.provers.Prover
import at.logic.provers.maxsat.MaxSATSolver
import at.logic.provers.minisat.MiniSATProver
import at.logic.transformations.herbrandExtraction.extractExpansionSequent
import at.logic.utils.executionModels.timeout._
import java.util.concurrent.TimeoutException
import scala.concurrent.duration._

class CutIntroException( msg: String ) extends Exception( msg )
class CutIntroIncompleteException( msg: String ) extends Exception( msg )
class CutIntroUncompressibleException( msg: String ) extends CutIntroException( msg )

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 */
class CutIntroEHSUnprovableException( msg: String ) extends CutIntroException( msg )

object CutIntroduction {

  // Public methods: timeout of one hour

  /**
   * Tries to introduce one cut with one quantifier to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   * @throws CutIntroException when the proof is not found.
   */
  def one_cut_one_quantifier( proof: LKProof, verbose: Boolean ) =
    execute( proof, false, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }
  /**
   * Tries to introduce one cut with one quantifier to the proof represented by
   * the ExpansionSequent.
   *
   * @param es The expansion sequent representing a proof for introducing a cut.
   * @param hasEquality True if the proof represented by es is in a theory
   *        modulo equality, false otherwise.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   * @throws CutIntroException when the proof is not found.
   */
  def one_cut_one_quantifier( es: ExpansionSequent, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, false, -1, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }
  /**
   * Tries to introduce one cut with as many quantifiers as possible to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   * @throws CutIntroException when the proof is not found.
   */
  def one_cut_many_quantifiers( proof: LKProof, verbose: Boolean ) =
    execute( proof, true, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }
  /**
   * Tries to introduce one cut with as many quantifiers as possible to the
   * proof represented by the ExpansionSequent.
   *
   * @param es The expansion sequent representing a proof for introducing a cut.
   * @param hasEquality True if the proof represented by es is in a theory
   *        modulo equality, false otherwise.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   * @throws CutIntroException when the proof is not found.
   */
  def one_cut_many_quantifiers( es: ExpansionSequent, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, true, -1, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }
  /**
   * Tries to introduce many cuts with one quantifier each to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param numcuts The (maximum) number of cuts to be introduced
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A list of cut-formulas.
   * @throws CutIntroException when the cut-formulas are not found.
   */
  def many_cuts_one_quantifier( proof: LKProof, numcuts: Int, verbose: Boolean ) =
    execute( proof, numcuts, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case ( None, _, _, None )      => throw new CutIntroIncompleteException( "Incomplete method. Proof not computed." )
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }
  /**
   * Tries to introduce many cuts with one quantifier each to the proof
   * represented by the ExpansionSequent.
   *
   * @param es The expansion sequent representing a proof for introducing a cut.
   * @param numcuts The (maximum) number of cuts to be introduced
   * @param hasEquality True if the proof represented by es is in a theory
   *        modulo equality, false otherwise.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A list of cut-formulas.
   * @throws CutIntroException when the proof is not found.
   */
  def many_cuts_one_quantifier( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, -1, numcuts, 1 hour, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case ( None, _, _, None )      => throw new CutIntroIncompleteException( "Incomplete method. Proof not computed." )
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }

  // Methods to be called for the experiments, only return status and log information
  def one_cut_one_quantifier_stat( proof: LKProof, timeout: Duration ) =
    execute( proof, false, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_one_quantifier_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Duration ) =
    execute( es, hasEquality, false, -1, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_many_quantifiers_stat( proof: LKProof, timeout: Duration ) =
    execute( proof, true, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_many_quantifiers_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Duration ) =
    execute( es, hasEquality, true, -1, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def many_cuts_one_quantifier_stat( proof: LKProof, numcuts: Int, timeout: Duration ) =
    execute( proof, numcuts, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def many_cuts_one_quantifier_stat( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, timeout: Duration ) =
    execute( es, hasEquality, -1, numcuts, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }

  /* 
   * ATTENTION
   * Actual implementation of cut introduction.
   * Here all the work is done and logging/time information is collected.
   * All other methods should call these execute methods and process the return values
   * according to the usage.
   * The two first 'execute' methods use the delta-table (by Stefan Hetzl) for computing grammars.
   * The two last methods use a maxsat formulation (by Sebastian Eberhard) for computing grammars.
   * Consequently, the two first methods will introduce one cut (with one or many quantifiers)
   * while the two last methods will introduce many cuts with one quantifier each.
   *
   */

  type LogTuple = ( Int, Int, Int, Int, Int, Int, Int, Int, Int, Int, Long, Long, Long, Long, Long, Long )
  def print_log_tuple( log: LogTuple ) = {
    println( "Total inferences in the input proof: " + log._1 );
    println( "Quantifier inferences in the input proof: " + log._2 );
    println( "Number of cuts introduced: " + log._3 );
    println( "Total inferences in the proof with cut(s): " + ( if ( log._4 == -1 ) "n/a" else log._4 ) );
    println( "Quantifier inferences in the proof with cut(s): " + ( if ( log._5 == -1 ) "n/a" else log._5 ) );
    println( "Size of the term set: " + log._6 );
    println( "Size of the minimal grammar: " + log._7 );
    println( "Number of minimal grammars: " + ( if ( log._8 == -1 ) "n/a" else log._8 ) );
    println( "Size of the canonical solution: " + ( if ( log._9 == -1 ) "n/a" else log._9 ) );
    println( "Size of the minimized solution: " + ( if ( log._10 == -1 ) "n/a" else log._10 ) );
    println( "Time for extracting the term set: " + log._11 );
    println( "Time for generating the delta-table: " + ( if ( log._12 == -1 ) "n/a" else log._12 ) );
    println( "Time for finding the grammar: " + log._13 );
    println( "Time for improving the solution: " + ( if ( log._14 == -1 ) "n/a" else log._14 ) );
    println( "Time for building the final proof: " + ( if ( log._15 == -1 ) "n/a" else log._15 ) );
    println( "Time for cleaning the structural rules of the final proof: " + ( if ( log._16 == -1 ) "n/a" else log._16 ) );
  }

  // Delta-table methods
  private def execute( proof: LKProof, manyQuantifiers: Boolean, timeout: Duration, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = extractExpansionSequent( clean_proof, false )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, manyQuantifiers, num_rules, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, manyQuantifiers: Boolean, num_lk_rules: Int, timeout: Duration, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val prover = hasEquality match {
      case true  => new EquationalProver()
      case false => new BasicProver()
    }

    var phase = ""
    var time = System.currentTimeMillis

    // The following information is returned (String, Tuple) by this method
    var status = "ok"

    val rulesLKProof = num_lk_rules
    val quantRules = quantRulesNumberET( ep )
    var numCuts = -1
    var rulesLKProofWithCut = -1
    var quantRulesWithCut = -1
    var termsetSize = -1
    var minimalGrammarSize = -1
    var numMinimalGrammars = -1
    var canonicalSolutionSize = -1
    var minimizedSolutionSize = -1
    var termsetExtractionTime: Long = -1
    var deltaTableGenerationTime: Long = -1
    var grammarFindingTime: Long = -1
    var improvingSolutionTime: Long = -1
    var buildProofTime: Long = -1
    var cleanStructuralRulesTime: Long = -1

    // From this point on, anything that involves modifying already
    // declared variables are concerned with time measurement and
    // logging. All the rest is the algorithm itself.

    val ( proof, error ) = try {
      withTimeout( timeout * 1000 ) {

        val endSequent = toFSequent( ep )
        if ( verbose ) println( "\nEnd sequent: " + endSequent )

        /********** Term set Extraction **********/
        phase = "termex"

        val termset = TermsExtraction( ep )

        termsetExtractionTime = System.currentTimeMillis - time
        time = System.currentTimeMillis
        termsetSize = termset.set.size
        if ( verbose ) println( "Size of term set: " + termset.set.size )

        /********** Delta Table Computation **********/
        phase = "delta_table_computation"

        val delta = manyQuantifiers match {
          case true  => new UnboundedVariableDelta()
          case false => new OneVariableDelta()
        }
        val eigenvariable = "α"
        val deltatable = new DeltaTable( termset.set, eigenvariable, delta )

        deltaTableGenerationTime = System.currentTimeMillis - time
        time = System.currentTimeMillis

        /********** Grammar finding **********/
        phase = "grammar_finding"

        val gs = ComputeGrammars.findValidGrammars( termset.set, deltatable, eigenvariable )
        val grammars = gs.map { case g => g.terms = termset; g }.sortWith( ( g1, g2 ) => g1.size < g2.size )

        // Adding up the generation of the delta-table so it is comparable to the other method.
        grammarFindingTime = deltaTableGenerationTime + System.currentTimeMillis - time
        time = System.currentTimeMillis
        if ( verbose ) println( "\nNumber of grammars: " + grammars.length )

        if ( grammars.length == 0 ) {
          throw new CutIntroUncompressibleException( "\nNo grammars found." +
            " The proof cannot be compressed using a cut with one universal quantifier.\n" )
        }

        /********** Proof Construction **********/
        val smallest = grammars.head.size
        val smallestGrammars = grammars.filter( g => g.size == smallest )

        minimalGrammarSize = smallest
        numMinimalGrammars = smallestGrammars.length
        if ( verbose ) println( "Smallest grammar-size: " + smallest )
        if ( verbose ) println( "Number of smallest grammars: " + smallestGrammars.length )

        improvingSolutionTime = 0
        buildProofTime = 0
        cleanStructuralRulesTime = 0

        val proofs = smallestGrammars.map {
          case grammar =>
            phase = "sol" // solving phase
            time = System.currentTimeMillis

            val cutFormulas = computeCanonicalSolutions( endSequent, grammar )
            assert( cutFormulas.length == 1, "This method should introduce one cut." )

            val ehs = new ExtendedHerbrandSequent( endSequent, grammar, cutFormulas )
            val ehs1 = hasEquality match {
              case true  => MinimizeSolution.applyEq( ehs, prover )
              case false => MinimizeSolution.apply( ehs, prover )
            }

            improvingSolutionTime += System.currentTimeMillis - time
            time = System.currentTimeMillis

            phase = "prcons" // proof construction

            val proof = buildProofWithCut( ehs1, prover )

            buildProofTime += System.currentTimeMillis - time
            time = System.currentTimeMillis

            val pruned_proof = CleanStructuralRules( proof.get )

            cleanStructuralRulesTime += System.currentTimeMillis - time

            ( pruned_proof, ehs1, lcomp( cutFormulas.head ), lcomp( ehs1.cutFormulas.head ) )
        }

        // Sort the list by size of proofs
        val sorted = proofs.sortWith( ( p1, p2 ) => rulesNumber( p1._1 ) < rulesNumber( p2._1 ) )
        val smallestProof = sorted.head._1
        val ehs = sorted.head._2

        numCuts = getStatistics( smallestProof ).cuts
        canonicalSolutionSize = sorted.head._3
        minimizedSolutionSize = sorted.head._4
        rulesLKProofWithCut = rulesNumber( smallestProof )
        quantRulesWithCut = quantRulesNumber( smallestProof )
        if ( verbose ) println( "\nMinimized cut formula: " + ehs.cutFormulas.head + "\n" )

        ( Some( smallestProof ), None )
      }
    } catch {
      case e: TimeoutException =>
        status = phase + "_timeout"
        ( None, Some( e ) )
      case e: OutOfMemoryError =>
        status = "cutintro_out_of_memory"
        ( None, Some( e ) )
      case e: StackOverflowError =>
        status = "cutintro_stack_overflow"
        ( None, Some( e ) )
      case e: CutIntroUncompressibleException =>
        status = "cutintro_uncompressible"
        ( None, Some( e ) )
      case e: CutIntroEHSUnprovableException =>
        status = "cutintro_ehs_unprovable"
        ( None, Some( e ) )
      case e: LKRuleCreationException =>
        status = "lk_rule_creation_exception"
        ( None, Some( e ) )
      case e: Exception =>
        status = "cutintro_other_exception"
        ( None, Some( e ) )
    }

    val tuple = ( rulesLKProof,
      quantRules,
      numCuts,
      rulesLKProofWithCut,
      quantRulesWithCut,
      termsetSize,
      minimalGrammarSize,
      numMinimalGrammars,
      canonicalSolutionSize,
      minimizedSolutionSize,
      termsetExtractionTime,
      deltaTableGenerationTime,
      grammarFindingTime,
      improvingSolutionTime,
      buildProofTime,
      cleanStructuralRulesTime )

    if ( verbose && error == None ) {
      println( "Status: " + status );
      print_log_tuple( tuple );
    }

    ( proof, status, tuple, error )
  }

  // MaxSat methods
  private def execute( proof: LKProof, n: Int, timeout: Duration, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = extractExpansionSequent( clean_proof, false )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, num_rules, n, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, num_lk_rules: Int, n: Int, timeout: Duration, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val prover = hasEquality match {
      case true  => new EquationalProver()
      case false => new BasicProver()
    }
    val maxsatsolver = MaxSATSolver.QMaxSAT

    var phase = ""
    var time = System.currentTimeMillis

    // The following information is returned (String, Tuple) by this method
    var status = "ok"

    val rulesLKProof = num_lk_rules
    val quantRules = quantRulesNumberET( ep )
    var numCuts = -1
    var rulesLKProofWithCut = -1
    var quantRulesWithCut = -1
    var termsetSize = -1
    var minimalGrammarSize = -1
    var numMinimalGrammars = -1
    var canonicalSolutionSize = -1
    var minimizedSolutionSize = -1
    var termsetExtractionTime: Long = -1
    var deltaTableGenerationTime: Long = -1
    var grammarFindingTime: Long = -1
    var improvingSolutionTime: Long = -1
    var buildProofTime: Long = -1
    var cleanStructuralRulesTime: Long = -1

    val ( proof, error ) = try {
      withTimeout( timeout * 1000 ) {

        val endSequent = toFSequent( ep )
        if ( verbose ) println( "\nEnd sequent: " + endSequent )

        /********** Terms Extraction **********/
        phase = "termex"

        val termset = TermsExtraction( ep )

        termsetExtractionTime = System.currentTimeMillis - time
        time = System.currentTimeMillis
        termsetSize = termset.set.size
        if ( verbose ) println( "Size of term set: " + termset.set.size )

        /********** Grammar finding **********/
        phase = "grammar_finding"

        val small_grammar = TreeGrammarDecomposition.applyStat( termset.set, n, MCSMethod.MaxSAT, maxsatsolver )
        val grammar = small_grammar match {
          case Some( g ) =>
            g.terms = termset; g
          case None =>
            throw new CutIntroUncompressibleException( "\nNo grammars found. The proof cannot be compressed." )
        }
        grammarFindingTime = System.currentTimeMillis - time
        time = System.currentTimeMillis

        // Although this shouldn't be the case, because of the grammar returned by
        // TreeGrammarDecomposition should either be None or some grammar with size > 0
        // we leave it here just to be sure
        if ( grammar.size == 0 ) {
          throw new CutIntroUncompressibleException( "\nNo grammars found. The proof cannot be compressed." )
        }

        /********** Proof Construction **********/

        // For the maxsat method, the number of eigenvariables in the grammar is
        // equivalent to the number of cuts in the final proof, since each cut has
        // only one quantifier.
        numCuts = grammar.numVars
        minimalGrammarSize = grammar.size
        if ( verbose ) println( "Smallest grammar-size: " + grammar.size )

        val cutFormulas = computeCanonicalSolutions( endSequent, grammar )
        // Average size of the cut-formula
        canonicalSolutionSize = ( cutFormulas.foldLeft( 0 )( ( acc, f ) => lcomp( f ) + acc ) ) / cutFormulas.length
        if ( verbose ) {
          println( "Cut formulas found: " )
          cutFormulas.foreach( f => println( f + "\n" ) )
        }

        // Build the proof only if introducing one cut
        // TODO: implement proof construction for multiple cuts
        if ( cutFormulas.length == 1 ) {

          val ehs = new ExtendedHerbrandSequent( endSequent, grammar, cutFormulas )
          time = System.currentTimeMillis

          phase = "prcons" // proof construction

          val proof = buildProofWithCut( ehs, prover )

          buildProofTime += System.currentTimeMillis - time
          time = System.currentTimeMillis

          val pruned_proof = CleanStructuralRules( proof.get )

          cleanStructuralRulesTime += System.currentTimeMillis - time
          rulesLKProofWithCut = rulesNumber( pruned_proof )
          quantRulesWithCut = quantRulesNumber( pruned_proof )

          ( Some( pruned_proof ), None )
        } else {
          status = "incomplete"
          ( None, None )
        }
      }
    } catch {
      case e: TimeoutException =>
        status = phase + "_timeout"
        ( None, Some( e ) )
      case e: OutOfMemoryError =>
        status = "cutintro_out_of_memory"
        ( None, Some( e ) )
      case e: StackOverflowError =>
        status = "cutintro_stack_overflow"
        ( None, Some( e ) )
      case e: Exception =>
        status = "cutintro_other_exception"
        ( None, Some( e ) )
      case e: TreeGrammarDecompositionException =>
        status = "tgd_failed"
        ( None, Some( e ) )
      case e: CutIntroUncompressibleException =>
        status = "cutintro_uncompressible"
        ( None, Some( e ) )
      case e: Exception =>
        status = "cutintro_other_exception"
        ( None, Some( e ) )
    }

    val tuple = ( rulesLKProof,
      quantRules,
      numCuts,
      rulesLKProofWithCut,
      quantRulesWithCut,
      termsetSize,
      minimalGrammarSize,
      numMinimalGrammars,
      canonicalSolutionSize,
      minimizedSolutionSize,
      termsetExtractionTime,
      deltaTableGenerationTime,
      grammarFindingTime,
      improvingSolutionTime,
      buildProofTime,
      cleanStructuralRulesTime )

    if ( verbose && error == None ) {
      println( "Status: " + status );
      print_log_tuple( tuple );
    }

    ( proof, status, tuple, error )
  }

  /**
   * Computes the canonical solution with multiple quantifiers from a generalized grammar.
   */
  def computeCanonicalSolutions( seq: FSequent, g: Grammar ): List[FOLFormula] = {

    val termset = g.terms
    val variables = g.slist.head._1

    val instantiated_f = g.u.foldRight( List[FOLFormula]() ) {
      case ( term, acc ) =>
        val freeVars = freeVariables( term )

        // Taking only the terms that contain alpha
        if ( freeVars.intersect( variables ).nonEmpty ) {
          val terms = termset.getTermTuple( term )
          val f = termset.getFormula( term )
          instantiateAll( f, terms ) :: acc
        } else acc
    }

    val c1 = And( instantiated_f )

    g.slist.foldLeft( List( c1 ) ) {
      case ( cut_formulas, ( variables, termset ) ) =>
        val ci = cut_formulas.head
        val forms = termset.foldLeft( List[FOLFormula]() ) {
          case ( acc, terms ) =>
            assert( variables.length == terms.length, "Number of eigenvariables different from number of terms in computation of canonical solution" )
            val subst = Substitution( variables.zip( terms ) )
            subst( ci ) :: acc
        }
        val ci_quant = variables.foldLeft( ci ) { ( f, v ) => AllVar( v, f ) }
        And( forms ) :: ci_quant :: cut_formulas.tail
      // The last term set contains only constants, so we drop the formula generated with it.
    }.tail.reverse
  }

  /**
   * Builds the final proof out of an extended Herbrand sequent.
   *
   * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
   */
  def buildProofWithCut( ehs: ExtendedHerbrandSequent, prover: Prover ): Option[LKProof] = {

    val endSequent = ehs.endSequent
    val cutFormula = ehs.cutFormulas.head
    val grammar = ehs.grammar
    val terms = grammar.terms

    assert( ehs.cutFormulas.length == 1, "buildProofWithCut: only one cut supported." )

    //Instantiate the cut formula with α_0,...,α_n-1, where n is the number of alphas in the ehs's grammar.
    //partialCutLeft.last ist the all-quantified cut formula, partialCutLeft.head ist the cut formula, with its
    //whole initial quantifier block instantiated to α_0,...,α_n-1.
    val alphas = ehs.grammar.eigenvariables

    //val partialCutLeft = (0 to alphas.length).toList.reverse.map(n => instantiateFirstN(cutFormula,alphas,n)).toList
    val cutLeft = instantiateAll( cutFormula, alphas )

    //Fully instantiate the cut formula with s[j=1...n][i] for all i.
    val cutRight = grammar.slist( 0 )._2.toList.foldRight( List[FOLFormula]() ) {
      case ( t, acc ) =>
        t.foldLeft( cutFormula ) { case ( f, sval ) => instantiate( f, sval ) } :: acc
    }

    //leftBranch and rightBranch correspond to the left and right branches of the proof in the middle of
    //p. 5; untilCut merges these together with a cut.

    //solvePropositional need only be called with the non-instantiated cutLeft (with the quantifier block in front)

    val seq = FSequent( ehs.antecedent ++ ehs.antecedent_alpha, cutLeft +: ( ehs.succedent ++ ehs.succedent_alpha ) )

    val proofLeft = prover.getLKProof( seq )
    val leftBranch = proofLeft match {
      case Some( proofLeft1 ) =>
        val s1 = uPart( grammar.u.filter( t => freeVariables( t ).intersect( grammar.eigenvariables ).nonEmpty ), proofLeft1, terms )

        //Add sequents to all-quantify the cut formula in the right part of s1
        ForallRightBlock( s1, cutFormula, alphas )

      case None => throw new CutIntroEHSUnprovableException( "ERROR: propositional part is not provable: " + seq )
    }

    val seq2 = FSequent( cutRight ++ ehs.antecedent, ehs.succedent )
    val proofRight = prover.getLKProof( seq2 )
    val rightBranch = proofRight match {
      case Some( proofRight1 ) => sPart( cutFormula, grammar.slist( 0 )._2, proofRight1 )
      case None                => throw new CutIntroEHSUnprovableException( "ERROR: propositional part is not provable: " + seq2 )
    }
    //trace( "done calling solvePropositional" )

    //Merge the left and right branches with a cut.
    val untilCut = CutRule( leftBranch, rightBranch, cutFormula )

    // Contracting the formulas that go to both branches of the cut
    val contractAnt = ehs.antecedent.foldRight( untilCut.asInstanceOf[LKProof] ) { case ( f, premise ) => ContractionLeftRule( premise, f ) }
    val contractSucc = ehs.succedent.foldRight( contractAnt.asInstanceOf[LKProof] ) { case ( f, premise ) => ContractionRightRule( premise, f ) }

    // Instantiating constant terms from U
    Some( uPart( grammar.u.filter( t => freeVariables( t ).intersect( grammar.eigenvariables ).isEmpty ), contractSucc, terms ) )
  }

  // Both methods bellow are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules( f: FOLFormula, lst: List[FOLTerm], ax: LKProof ): LKProof = ( f, lst ) match {
    case ( _, Nil ) => ax
    case ( AllVar( _, _ ), h :: t ) =>
      val newForm = instantiate( f, h )
      ForallLeftRule( genWeakQuantRules( newForm, t, ax ), newForm, f, h )
    case ( ExVar( _, _ ), h :: t ) =>
      val newForm = instantiate( f, h )
      ExistsRightRule( genWeakQuantRules( newForm, t, ax ), newForm, f, h )
  }

  /**
   * Proves the u-part of a grammar.
   *
   */
  private def uPart( us: List[types.U], ax: LKProof, terms: TermSet ): LKProof = {
    us.foldLeft( ax ) {
      case ( ax, term ) =>
        //Get the arguments of a single u
        val set = terms.getTermTuple( term )
        val f = terms.getFormula( term )

        f match {
          case AllVar( _, _ ) =>
            try {
              ContractionLeftRule( genWeakQuantRules( f, set, ax ), f )
            } catch {
              // Not able to contract the formula because it was the last
              // substitution
              case e: LKRuleCreationException => genWeakQuantRules( f, set, ax )
            }
          case ExVar( _, _ ) =>
            try {
              ContractionRightRule( genWeakQuantRules( f, set, ax ), f )
            } catch {
              case e: LKRuleCreationException => genWeakQuantRules( f, set, ax )
            }
        }
    }
  }

  private def sPart( cf: FOLFormula, s: types.S, p: LKProof ): LKProof = {
    var first = true

    s.toList.foldLeft( p ) {
      case ( p, t ) =>

        //1. Partially instantiate the cut formula.
        //val pcf = (0 to t.length).toList.reverse.map(n => instantiateFirstN(cf,t,n)).toList

        //2. Starting from p, in which pcf[0] occurs, work down, adding quantifiers, until we get 
        //   the fully quantified cf back.
        val newP = ForallLeftBlock( p, cf, t )

        //3. If this is not the first time we build cf, 
        //   cf is already present in p and we can do away with its second,
        //   newly generated instance through a contraction rule.
        if ( first ) {
          first = false
          newP
        } else {
          ContractionLeftRule( newP, cf )
        }
    }
  }
}

