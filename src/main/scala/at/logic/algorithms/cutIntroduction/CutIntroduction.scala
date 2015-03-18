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
import at.logic.algorithms.interpolation.ExtractInterpolant
import at.logic.algorithms.fol.simplify.simplify

import scala.collection.immutable.HashSet

class CutIntroException( msg: String ) extends Exception( msg )
class CutIntroIncompleteException( msg: String ) extends Exception( msg )
class CutIntroUncompressibleException( msg: String ) extends CutIntroException( msg )

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 */
class CutIntroEHSUnprovableException( msg: String ) extends CutIntroException( msg )

object CutIntroduction extends at.logic.utils.logging.Logger {

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
    execute( proof, false, 3600, verbose ) match {
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
    execute( es, hasEquality, false, -1, 3600, verbose ) match {
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
    execute( proof, true, 3600, verbose ) match {
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
    execute( es, hasEquality, true, -1, 3600, verbose ) match {
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
    execute( proof, numcuts, 3600, verbose ) match {
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
    execute( es, hasEquality, -1, numcuts, 3600, verbose ) match {
      case ( Some( p ), _, _, None ) => p
      case ( None, _, _, Some( e ) ) => throw e
      case ( None, _, _, None )      => throw new CutIntroIncompleteException( "Incomplete method. Proof not computed." )
      case _                         => throw new CutIntroException( "Wrong return value in cut introduction." )
    }

  // Methods to be called for the experiments, only return status and log information
  def one_cut_one_quantifier_stat( proof: LKProof, timeout: Int ) =
    execute( proof, false, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_one_quantifier_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Int ) =
    execute( es, hasEquality, false, -1, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_many_quantifiers_stat( proof: LKProof, timeout: Int ) =
    execute( proof, true, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def one_cut_many_quantifiers_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Int ) =
    execute( es, hasEquality, true, -1, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def many_cuts_one_quantifier_stat( proof: LKProof, numcuts: Int, timeout: Int ) =
    execute( proof, numcuts, timeout, false ) match {
      case ( _, status, log, _ ) => ( status, log )
    }
  def many_cuts_one_quantifier_stat( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, timeout: Int ) =
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
  private def execute( proof: LKProof, manyQuantifiers: Boolean, timeout: Int, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = extractExpansionSequent( clean_proof, false )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, manyQuantifiers, num_rules, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, manyQuantifiers: Boolean, num_lk_rules: Int, timeout: Int, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

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

        val gs = ComputeGrammars.findValidGrammars( termset, deltatable, eigenvariable )
        val grammars = gs.sortWith( ( g1, g2 ) => g1.size < g2.size )

        // Adding up the generation of the delta-table so it is comparable to the other method.
        grammarFindingTime = deltaTableGenerationTime + System.currentTimeMillis - time
        time = System.currentTimeMillis
        if ( verbose ) println( "\nNumber of grammars: " + grammars.length )

        if ( grammars.length == 0 ) {
          throw new CutIntroUncompressibleException( "\nNo grammars found." +
            " The proof cannot be compressed using one cut.\n" )
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

            val cutFormulas = computeCanonicalSolutions( grammar )
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
      case e: TimeOutException =>
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
  private def execute( proof: LKProof, n: Int, timeout: Int, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = extractExpansionSequent( clean_proof, false )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, num_rules, n, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, num_lk_rules: Int, n: Int, timeout: Int, verbose: Boolean ): ( Option[LKProof], String, LogTuple, Option[Throwable] ) = {

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

        val small_grammar = TreeGrammarDecomposition( termset, n, MCSMethod.MaxSAT, maxsatsolver )
        val grammar = small_grammar match {
          case Some( g ) => g
          case None =>
            throw new CutIntroUncompressibleException( "\nNo grammars found. The proof cannot be compressed." )
        }
        grammarFindingTime = System.currentTimeMillis - time
        time = System.currentTimeMillis

        println( "Grammar\n" + grammar )

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

        val cutFormulas = computeCanonicalSolutions( grammar )
        // Average size of the cut-formula
        canonicalSolutionSize = ( cutFormulas.foldLeft( 0 )( ( acc, f ) => lcomp( f ) + acc ) ) / cutFormulas.length
        if ( verbose ) {
          println( "Cut formulas found: " )
          cutFormulas.foreach( f => println( f + "\n" ) )
        }

        // Build the proof only if introducing one cut
        // TODO: implement proof construction for multiple cuts
        //        if ( cutFormulas.length == 1 ) {

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
        /*        } else {
          status = "incomplete"
          ( None, None )
        }*/
      }
    } catch {
      case e: TimeOutException =>
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
   * Computes the canonical solution with multiple quantifiers from a MultiGrammar,
   * i.e. the list \forall x_1...x_n C_1, ...., \forall x_1 C_n.
   */
  def computeCanonicalSolutions( g: MultiGrammar ): List[FOLFormula] = {

    //val termset = g.terms
    val variables = g.ss.head._1

    val instantiated_f = g.us.keys.foldRight( List[FOLFormula]() ) {
      case ( formula, acc ) => {
        val termlistlist = g.us( formula )
        acc ++ termlistlist.foldLeft( List[FOLFormula]() ) {
          case ( acc, termlist ) => {
            val freeVars = freeVariables( termlist )

            if ( freeVars.intersect( variables ).nonEmpty ) {
              val i_f = instantiateAll( formula, termlist )
              val f = formula match {
                case ExVar( _ )  => Neg( i_f )
                case AllVar( _ ) => i_f
              }
              f :: acc
            } else acc
          }
        }
      }
    }

    val c1 = And( instantiated_f )

    g.ss.foldLeft( List( c1 ) ) {
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

  private def getCutImpl( cf: FOLFormula, alpha: List[FOLVar], ts: List[List[FOLTerm]] ) = {
    val ant = instantiateAll( cf, alpha )
    val succ = And( ts.map( termlist => instantiateAll( cf, termlist ) ).toList )
    Imp( ant, succ )
  }


  /**
   * Builds the final proof out of an extended Herbrand sequent.
   *
   * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
   */
  def buildProofWithCut( ehs: ExtendedHerbrandSequent, prover: Prover ): Option[LKProof] = {

    val endSequent = ehs.endSequent
    val cutFormulas = ehs.cutFormulas
    val grammar = ehs.grammar

    trace( "grammar: " + grammar )
    trace( "cutFormulas: " + cutFormulas )

    val alphas = grammar.eigenvariables

    // As an efficiency improvement, we treat the non-quantified part of the end-sequent
    // separately (since it never needs to be instantiated).
    val quantPart = FSequent( endSequent.antecedent.filter {
      case AllVar( _ ) => true
      case _           => false
    },
      endSequent.succedent.filter {
        case ExVar( _ ) => true
        case _          => false
      } )

    // In our setting, we work with a sequent instead of a formula F as in the paper.
    // The following sequent corresponds to that formula.
    val F = FSequent( ehs.quant_l, ehs.quant_r )

    // Define the U_i from the paper. Since our F is more general, also U is more general:
    // instead of a list of lists of terms (corresponding to the term instances of the quantifiers
    // in the formula F), we have two lists Uleft and Uright. The intended semantics is that
    // Uleft(i) corresponds to U_i from the paper for the left part of the sequent, and analogously
    // for URight(i).
    //
    // More precisely: Uleft(i)(j)(k)(l) is the k'th U_i-instance of the l'th quantifier of the j'th formula
    // in the antecedent. Similarily for Uright.

    // TODO: rewrite this to have getUs return a Seq[Map[FOLFormula, Seq[Seq[FOLTerm]]]]

    def getUs( fs: Seq[FOLFormula] ): Seq[Seq[Seq[Seq[FOLTerm]]]] =
      ( 0 to alphas.size ).map( i => fs.map( f => {
        val termlistlist = grammar.us( f )
        termlistlist.filter( termlist => freeVariables( termlist ).intersect( alphas.take( i ) ).isEmpty )
      } ) )

    val Uleft = getUs( F.antecedent.asInstanceOf[Seq[FOLFormula]] )
    val Uright = getUs( F.succedent.asInstanceOf[Seq[FOLFormula]] )

    trace( "Uleft : " + Uleft )
    trace( "Uright : " + Uright )

    // define the A_i
    val A = ( cutFormulas zip alphas ).map {
      case ( cf, ev ) => {
        trace( "computing A" )
        trace( "instantiating " + cf + " with " + ev )
        instantiateAll( cf, ev :: Nil )
      }
    }

    trace( "A: " + A )

    // define the sequent corresponding to F[x \ U_i]
    val FU = ( 0 to alphas.size ).map( i => FSequent(
      ( F.antecedent zip Uleft( i ) ).flatMap { case ( f, terms ) => instantiateAll( f.asInstanceOf[FOLFormula], terms ) },
      ( F.succedent zip Uright( i ) ).flatMap { case ( f, terms ) => instantiateAll( f.asInstanceOf[FOLFormula], terms ) } ) )

    trace( "FU: " + FU )

    // define A_i[x \ S_i]
    val AS = ( 0 to alphas.size - 1 ).map( i => grammar.ss( i )._2.map( s => instantiateAll( cutFormulas( i ), s ) ) )

    trace( "AS: " + AS )

    // define the CI_i
    val cutImplications = ( 0 to alphas.size - 1 ).map( i => getCutImpl( cutFormulas( i ), alphas( i ) :: Nil, grammar.ss( i )._2 ) )

    // compute the A_i' via interpolation
    // TODO: increase performance by feeding existing proofs to the
    // interpolation algorithm?
    val Aprime = ( 1 to alphas.size ).reverse.foldLeft( Nil: List[FOLFormula] ) {
      case ( acc, i ) => {
        val allf = FU( 0 ) compose ( new FSequent( ehs.prop_l, ehs.prop_r ) )
        val posf = FU( i - 1 ) compose ( new FSequent( ehs.prop_l, ehs.prop_r ) )
        val negf = allf diff posf
        val neg = negf compose ( new FSequent( cutImplications.take( i - 1 ), Nil ) )
        val pos = posf compose ( new FSequent( AS( i - 1 ), acc ) )
        val interpolant = ExtractInterpolant( neg, pos, prover )
        val res = And( A( i - 1 ), interpolant )
        val res2 = simplify( res )
        acc :+ res2
      }
    }.reverse

    val cutFormulasPrime = ( Aprime zip Aprime.indices ).map { case ( a, i ) => AllVar( alphas( i ), a ) }

    // define A'_i[x \ S_i]
    val AprimeS = ( 0 to alphas.size - 1 ).map( i => grammar.ss( i )._2.map( s => instantiateAll( cutFormulasPrime( i ), s ) ) )

    // define L_1
    val L1 = FSequent( ehs.antecedent ++ ehs.antecedent_alpha, Aprime ++ ehs.succedent ++ ehs.succedent_alpha )

    trace( "L1: " + L1 )

    // define the R_i
    val R = ( 0 to alphas.size - 1 ).map( i =>
      FSequent( AprimeS( i ).toSeq ++ ehs.prop_l, Aprime.drop( i ) ++ ehs.prop_r ).compose(
        FU( i ) ) )

    trace( "R: " + R )

    // we need a proof of L_1
    val Lproof = prover.getLKProof( L1 )

    // we need proofs of R_1, ..., R_n
    val Rproofs = R.map( s => prover.getLKProof( s ) )

    ( ( Rproofs :+ Lproof ) zip ( R :+ L1 ) ).foreach {
      case ( None, seq ) => throw new CutIntroEHSUnprovableException( "ERROR: propositional part is not provable: " + seq )
      case _             => {}
    }

    // To keep a nice induction invariant, we introduce the quantified part of the end-sequent
    // via weakening (so that we can always contract later on).
    val Lproof_ = WeakeningRightMacroRule( WeakeningLeftMacroRule( Lproof.get, quantPart.antecedent ), quantPart.succedent )

    // As above, we introduce the quantified cut-formula via weakening for keeping the invariant
    val Rproofs_ = ( Rproofs zip cutFormulasPrime ).map { case ( p, cf ) => WeakeningLeftRule( p.get, cf ) }

    // This is the recursive construction obtaining the final proof by combining the proofs
    // of L_1, R_1, ..., R_n with appropriate inference rules as in the paper.
    val proof = ( 0 to alphas.size - 1 ).foldLeft( Lproof_ )( ( lproof, i ) => {
      val left = buildLeftPart( i, quantPart, Aprime, Uleft, Uright, alphas, cutFormulasPrime( i ), lproof )
      trace( " Rproofs_( " + i + " ).root: " + Rproofs_( i ).root )
      val right = buildRightPart( Rproofs_( i ), cutFormulasPrime( i ), grammar.ss( i )._2.map( _.head ).toList )
      trace( "right part ES: " + right.root )
      val cut = CutRule( left, right, cutFormulasPrime( i ) )
      val cont1 = ContractionMacroRule( cut, FU( i + 1 ), false )
      val cont2 = ContractionMacroRule( cont1, FSequent( ehs.prop_l, ehs.prop_r ), false )
      ContractionMacroRule( cont2, FSequent( Nil, Aprime.drop( i + 1 ) ), false )
    } )

    def finish( p: LKProof, fs: Seq[FOLFormula], instances: Seq[Seq[Seq[FOLTerm]]] ) =
      ( fs zip instances ).foldLeft( p ) { case ( proof, ( f, is ) ) => genWeakQuantRules( f, is, proof ) }

    val proof_ = finish( proof, quantPart.antecedent.asInstanceOf[Seq[FOLFormula]], Uleft( alphas.size ) )
    val proof__ = finish( proof_, quantPart.succedent.asInstanceOf[Seq[FOLFormula]], Uright( alphas.size ) )

    trace( "proof__.root: " + proof__.root )

    Some( proof__ )
  }

  /**
   * Construct the proof
   *
   * \forall G, G[U_i] :- D[U_i], \exists D, A_{i}[alpha_{i}], ..., A_n
   * ----------------------------------------------------------------------- \forall_l, \exists_r, c_l, c_r
   * \forall G, G[U_{i+1}] :- D[U_{i+1}], \exists D, A_{i}, ..., A_n
   * ----------------------------------------------------------------------------- \forall_r
   * \forall G, G[U_{i+1}] :- D[U_{i+1}], \exists D, (\forall x) A_{i}[x], ..., A_n
   */
  private def buildLeftPart( i: Int, es: FSequent, A: Seq[FOLFormula], Uleft: Seq[Seq[Seq[Seq[FOLTerm]]]], Uright: Seq[Seq[Seq[Seq[FOLTerm]]]], alphas: Seq[FOLVar], cf: FOLFormula, proof: LKProof ) =
    {
      def myWeakQuantRules( proof: LKProof, fs: Seq[FOLFormula], instances: Seq[Pair[Seq[Seq[FOLTerm]], Seq[Seq[FOLTerm]]]] ) =
        ( fs zip instances ).foldLeft( proof ) { case ( proof, ( f, ( ui, uip ) ) ) => genWeakQuantRules( f, ui diff uip, proof ) }

      val p1 = myWeakQuantRules( proof, es.antecedent.asInstanceOf[Seq[FOLFormula]], Uleft( i ) zip Uleft( i + 1 ) )
      val p2 = myWeakQuantRules( p1, es.succedent.asInstanceOf[Seq[FOLFormula]], Uright( i ) zip Uright( i + 1 ) )

      ForallRightRule( p2, A( i ), cf, alphas( i ) )
    }

  /**
   * Construct the proof
   *
   * A_i[S_i], G[U_i] :- D[U_i], A_{i+1}, ..., A_n
   * --------------------------------------------- \forall_l
   * (\forall x) A_i[x], G[U_i] :- D[U_i], A_{i+1}, ..., A_n
   *
   * (to be used to cut against the result of buildLeftPart)
   */
  private def buildRightPart( proof: LKProof, a: FOLFormula, s: Seq[FOLTerm] ) =
    {
      trace( "calling buildRightPart" )
      trace( "a: " + a )
      trace( "s: " + s )
      genWeakQuantRules( a, s.map( _ :: Nil ), proof )
    }

  // Both methods below are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules( f: FOLFormula, lst: Seq[Seq[FOLTerm]], ax: LKProof ): LKProof = {
    trace( "calling genWeakQuantRules" )
    trace( "f: " + f )
    trace( "lst: " + lst )
    ( f, lst ) match {
      case ( _, Nil ) => ax
      case ( AllVar( _, _ ), h :: t ) =>
        val newForm = instantiateAll( f, h )
        ContractionLeftRule( ForallLeftBlock( genWeakQuantRules( f, t, ax ), f, h ), f )
      case ( ExVar( _, _ ), h :: t ) =>
        val newForm = instantiateAll( f, h )
        ContractionRightRule( ExistsRightBlock( genWeakQuantRules( f, t, ax ), f, h ), f )
    }
  }
}

