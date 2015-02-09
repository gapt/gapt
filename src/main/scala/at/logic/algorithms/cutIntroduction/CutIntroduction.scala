/**
 * Cut introduction algorithm
 *
 *
 */
package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.cutIntroduction.Deltas._
import at.logic.proofs.expansionTrees.{ ExpansionSequent, toSequent, quantRulesNumber => quantRulesNumberET }
import at.logic.proofs.lk
import at.logic.proofs.lk._
import at.logic.proofs.lk.algorithms.{ quantRulesNumber, _ }
import at.logic.proofs.lk.base._
import at.logic.language.fol._
import at.logic.language.hol.HOLFormula
import at.logic.provers.basicProver._
import at.logic.provers.eqProver._
import at.logic.provers.Prover
import at.logic.provers.maxsat.MaxSATSolver
import at.logic.provers.minisat.MiniSATProver
import at.logic.transformations.herbrandExtraction.extractExpansionSequent
import at.logic.utils.executionModels.timeout._

class CutIntroException( msg: String ) extends Exception( msg )
class CutIntroUncompressibleException( msg: String ) extends CutIntroException( msg )
class CutIntroNotYetImplementedException( msg: String ) extends CutIntroException( msg )

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
      case ( None, _, _, None )      => throw new CutIntroNotYetImplementedException( "Proof construction for n>1 cuts not yet implemented" )
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

        val endSequent = toSequent( ep )
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

            val cutFormulas = computeCanonicalSolution( grammar )

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

            ( pruned_proof, ehs1, lcomp( cutFormulas( 0 ) ), lcomp( ehs1.cutFormulas( 0 ) ) )
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
        if ( verbose ) println( "\nMinimized cut formula: " + ehs.cutFormulas( 0 ) + "\n" )

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

        val endSequent = toSequent( ep )
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

        // TODO: fix this when proof generation and ExtendedHerbrandSequent are capable of solutions > 1 cuts
        // Note that to this point ExtHSeq for 1 cut, many quantifiers
        //                         minimizing solution for 1 cut, many quantifiers
        //                         proof construction for 1 cut, many quantifiers
        // is implemented
        /********** Canonical Solution **********/
        improvingSolutionTime = 0
        phase = "sol" // solving phase
        time = System.currentTimeMillis

        val cutFormulas = computeCanonicalSolution( grammar )

        var ehs = new ExtendedHerbrandSequent( endSequent, grammar, cutFormulas )
        // improve solution in case of 1 cut
        if ( ehs.cutFormulas.size == 1 ) {
          // TODO: this is only executed when dealing with proofs having 1 cut
          ehs = hasEquality match {
            case true  => MinimizeSolution.applyEq( ehs, prover )
            case false => MinimizeSolution.apply( ehs, prover )
          }

          improvingSolutionTime += System.currentTimeMillis - time
          time = System.currentTimeMillis
          /********** Proof Construction **********/
          phase = "prcons"

          // For the maxsat method, the number of eigenvariables in the grammar is
          // equivalent to the number of cuts in the final proof, since each cut has
          // only one quantifier.
          numCuts = grammar.numVars
          minimalGrammarSize = grammar.size

          buildProofTime = 0
          cleanStructuralRulesTime = 0

          phase = "prcons" // proof construction

          val proof = buildProofWithCut( ehs, prover )

          buildProofTime += System.currentTimeMillis - time
          time = System.currentTimeMillis

          val prunedProof = CleanStructuralRules( proof.get )

          cleanStructuralRulesTime += System.currentTimeMillis - time

          numCuts = getStatistics( prunedProof ).cuts
          canonicalSolutionSize = lcomp( cutFormulas( 0 ) )
          minimizedSolutionSize = lcomp( ehs.cutFormulas( 0 ) )
          rulesLKProofWithCut = rulesNumber( prunedProof )
          quantRulesWithCut = lk.algorithms.quantRulesNumber( prunedProof )
          if ( verbose ) println( "\nMinimized cut formula: " + ehs.cutFormulas( 0 ) + "\n" )

          if ( verbose ) println( "Smallest grammar-size: " + grammar.size )

          ( Some( prunedProof ), None )
        } else {
          // returning None proof, since proof building for > 1 cuts is not yet implemented
          improvingSolutionTime = 0
          numCuts = ehs.cutFormulas.size
          minimalGrammarSize = grammar.size
          buildProofTime = 0
          cleanStructuralRulesTime = 0
          canonicalSolutionSize = lcomp( cutFormulas( 0 ) )
          minimizedSolutionSize = lcomp( ehs.cutFormulas( 0 ) )
          rulesLKProofWithCut = 0
          quantRulesWithCut = 0
          ( None, None )
        }
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
      case e: CutIntroNotYetImplementedException =>
        status = "cutintro_not_yet_implemented"
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
      println( "Status: " + status )
      print_log_tuple( tuple )
    }

    ( proof, status, tuple, error )
  }

  /**
   * Computes the canonical solution with multiple quantifiers from a generalized grammar.
   */
  def computeCanonicalSolution( g: Grammar ): List[FOLFormula] = {

    // generating all (U,,i,,,eigenvariables)
    def getUEvsTuples( u: List[FOLTerm], slist: List[( List[FOLVar], Set[List[FOLTerm]] )] ): List[Tuple2[List[FOLTerm], List[FOLVar]]] = {
      // propagate all terms to obtain Ui
      return slist match {
        case Nil => Nil
        case _ => {
          val nextU = propagateTerms( u, slist( 0 )._2, slist( 0 )._1 )
          ( u, slist( 0 )._1 ) :: getUEvsTuples( nextU, slist.drop( 1 ) )
        }
      }
    }
    val uevstuples = getUEvsTuples( g.u, g.slist )
    // generate a solution of the form C,,1,, , C,,1,, \supset C,,2,, , ..., C,,n-1,, \supset C,,n,,
    val Cs = uevstuples.map( tuple => computeCanonicalSolutionComponent( tuple._1, tuple._2, g.terms ) )
    if ( Cs.size == 1 ) {
      return Cs
    } else {
      return Cs.sliding( 2 ). // generate lists [C1,C2],[C2,C3],...,[Cn-1,Cn]
        foldLeft( List[FOLFormula]( Cs( 0 ) ) )( ( solution, C ) => {
          solution :+ Imp( C( 0 ), C( 1 ) )
        } )
    }
  }

  /**
   * Takes a grammar U o,,x,,1,,,..., x,,m,,,, S,,1,, o ... o S,,n,, and returns a list of terms
   * U,,1,, = U[x,,1,,\S,,1,1,,]...[x,,m,,\S,,1,m,,], where every occurrence of x,,i,,
   * in every term in U gets substituted by every term in S,,1,,
   * @param u U
   * @param s1 S,,1,,
   * @param eigenvariables the eigenvariables o,,\alpha_1,...,\alpha_n,,
   * @return the produced list of terms U,,1,,
   */
  def propagateTerms( u: List[FOLTerm], s1: Set[List[FOLTerm]], eigenvariables: List[FOLVar] ): List[FOLTerm] = {

    val subs = s1.map( sterm => Substitution( eigenvariables.zip( sterm ) ) ).toList
    val u1 = u.foldLeft( List[FOLTerm]() )( ( acc, u0 ) => subs.map( sub => sub( u0 ) ) ::: acc )
    u1
  }

  /**
   * Takes a list of folterms U,,i,, (in case U,,0,, = U), a list of eigenvariables
   * which are treated in this solution component and all terms produced by the underlying grammar (i.e. g.terms)
   * an produces a formulas C,,i+1,, which appears in a canonical solution of the form
   * C,,1,,,C,,1,, \supset C,,2,,, C,,2,, \supset C,,3,,, ..., C,,n,, \supset C,,n+1,,
   * @param Ui termset (U,,0,, = U, U,,i,, = U\sigma,,1,,...\sigma,,i,,)
   * @param eigenvariables list of variables treated as eigenvariables (e.g. o,,\alpha,,1,,,\alpha,,2,,,,)
   * @param allterms all terms produced by the underlying grammar (i.e. g.terms)
   * @return C,,i+1,,
   */
  def computeCanonicalSolutionComponent( Ui: List[FOLTerm], eigenvariables: List[FOLVar], allterms: TermSet ): FOLFormula = {

    //assert (g.slist.size == 1, "computeCanonicalSolution: only simple grammars supported.")

    val terms = allterms
    val varName = "x"

    val xFormulas = Ui.foldRight( List[FOLFormula]() ) {
      case ( term, acc ) =>
        val freeVars = freeVariables( term )

        // Taking only the terms that contain alpha
        if ( freeVars.intersect( eigenvariables ).nonEmpty ) {
          val set = terms.getTermTuple( term )
          val f = terms.getFormula( term )

          //Some subset of g's eigenvariables occurs in every term. This generates
          //substitutions to replace each occurring EV a_i with a quantified variables x_i.
          val xterms = set.map( t => {
            val vars = createFOLVars( varName, eigenvariables.length + 1 )
            val allEV = eigenvariables.zip( vars )
            val occurringEV = collectVariables( t ).filter( v => eigenvariables.contains( v ) ).distinct

            // If the term is a constant, this should return t itself
            val t1 = allEV.filter( e => occurringEV.contains( e._1 ) ).foldLeft( t )( ( t, e ) => Substitution( e._1, e._2 ).apply( t ) )
            t1
          } )

          val inst = instantiateAll( f, xterms )
          inst :: acc

        } else acc
    }
    ( 0 to ( eigenvariables.size - 1 ) ).reverse.toList.foldLeft( And( xFormulas ) ) { ( f, n ) => AllVar( FOLVar( varName + "_" + n ), f ) }
  }

  /**
   * Builds the final proof out of an extended Herbrand sequent.
   *
   * For details, see p.5 of "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)".
   */
  def buildProofWithCut( ehs: ExtendedHerbrandSequent, prover: Prover ): Option[LKProof] = {

    val endSequent = ehs.endSequent
    //TODO: begin here to implement proof building with > 1 cuts
    if ( ehs.cutFormulas.size == 1 ) {
      val cutFormula = ehs.cutFormulas( 0 )
      val grammar = ehs.grammar
      val terms = grammar.terms

      assert( grammar.slist.size == 1, "buildProofWithCut: only simple grammars supported." )

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
      return Some( uPart( grammar.u.filter( t => freeVariables( t ).intersect( grammar.eigenvariables ).isEmpty ), contractSucc, terms ) )
    }
    throw new CutIntroNotYetImplementedException( "Trying to build a proof from an extended Herbrand Sequent with > 1 cuts. Not yet implemented." )
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

