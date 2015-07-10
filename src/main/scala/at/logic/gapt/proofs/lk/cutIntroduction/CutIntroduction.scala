/**
 * Cut introduction algorithm
 *
 *
 */
package at.logic.gapt.proofs.lk.cutIntroduction

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.findMinimalGrammar
import at.logic.gapt.proofs.expansionTrees.{ quantRulesNumber => quantRulesNumberET, toShallow, ExpansionSequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.lk.cutIntroduction.Deltas.{ OneVariableDelta, UnboundedVariableDelta }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.basicProver._
import at.logic.gapt.provers.eqProver._
import at.logic.gapt.provers.maxsat.{ QMaxSAT, MaxSATSolver }
import at.logic.gapt.utils.executionModels.timeout._
import at.logic.gapt.utils.logging.{ CollectMetrics, metrics, Logger }
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

object CutIntroduction extends Logger {

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
    execute( proof, false, 3600, verbose ).get
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
    execute( es, hasEquality, false, -1, 3600, verbose ).get

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
    execute( proof, true, 3600, verbose ).get
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
    execute( es, hasEquality, true, -1, 3600, verbose ).get
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
    execute( proof, numcuts, 3600, verbose ) getOrElse {
      throw new CutIntroIncompleteException( "Incomplete method. Proof not computed." )
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
    execute( es, hasEquality, -1, numcuts, 3600, verbose ) getOrElse {
      throw new CutIntroIncompleteException( "Incomplete method. Proof not computed." )
    }

  def one_cut_one_quantifier_stat( proof: LKProof, timeout: Int ) =
    execute( proof, false, timeout, false )
  def one_cut_one_quantifier_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Int ) =
    execute( es, hasEquality, false, -1, timeout, false )
  def one_cut_many_quantifiers_stat( proof: LKProof, timeout: Int ) =
    execute( proof, true, timeout, false )
  def one_cut_many_quantifiers_stat( es: ExpansionSequent, hasEquality: Boolean, timeout: Int ) =
    execute( es, hasEquality, true, -1, timeout, false )
  def many_cuts_one_quantifier_stat( proof: LKProof, numcuts: Int, timeout: Int ) =
    execute( proof, numcuts, timeout, false )
  def many_cuts_one_quantifier_stat( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, timeout: Int ) =
    execute( es, hasEquality, -1, numcuts, timeout, false )

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
  private def execute( proof: LKProof, manyQuantifiers: Boolean, timeout: Int, verbose: Boolean ): Option[LKProof] = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = LKToExpansionProof( clean_proof )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, manyQuantifiers, num_rules, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, manyQuantifiers: Boolean, num_lk_rules: Int, timeout: Int, verbose: Boolean ): Option[LKProof] = {

    val prover = hasEquality match {
      case true  => new EquationalProver()
      case false => new BasicProver()
    }

    metrics.value( "quant_input", quantRulesNumberET( ep ) )
    metrics.value( "inf_input", num_lk_rules )

    val endSequent = toShallow( ep )
    if ( verbose ) println( "\nEnd sequent: " + endSequent )

    /********** Term set Extraction **********/
    val termset = metrics.time( "termset" ) { TermsExtraction( ep ) }

    metrics.value( "termset", termset.set.size )
    if ( verbose ) println( "Size of term set: " + termset.set.size )

    /********** Delta Table Computation **********/
    val delta = manyQuantifiers match {
      case true  => new UnboundedVariableDelta()
      case false => new OneVariableDelta()
    }
    val eigenvariable = "α"
    val deltatable = metrics.time( "dtable" ) { new DeltaTable( termset.set, eigenvariable, delta ) }

    /********** Grammar finding **********/
    val grammars = metrics.time( "grammar" ) { ComputeGrammars.findValidGrammars( termset, deltatable, eigenvariable ).sortWith( ( g1, g2 ) => g1.size < g2.size ) }

    if ( verbose ) println( "\nNumber of grammars: " + grammars.length )

    if ( grammars.length == 0 ) {
      throw new CutIntroUncompressibleException( "No grammars found." +
        " The proof cannot be compressed using one cut." )
    }

    /********** Proof Construction **********/
    val smallest = grammars.head.size
    val smallestGrammars = grammars.filter( g => g.size == smallest )

    metrics.value( "mingrammar", smallest )
    metrics.value( "num_mingram", smallestGrammars.size )
    if ( verbose ) println( "Smallest grammar-size: " + smallest )
    if ( verbose ) println( "Number of smallest grammars: " + smallestGrammars.length )

    val proofs = smallestGrammars.map { grammar =>
      val ( cutFormulas, ehs1 ) = metrics.time( "sol" ) {
        val cutFormulas = computeCanonicalSolutions( grammar )
        assert( cutFormulas.length == 1, "This method should introduce one cut." )

        val ehs = new ExtendedHerbrandSequent( endSequent, grammar, cutFormulas )
        val ehs1 = hasEquality match {
          case true  => MinimizeSolution.applyEq( ehs, prover )
          case false => MinimizeSolution.apply( ehs, prover )
        }

        ( cutFormulas, ehs1 )
      }

      val proof = metrics.time( "prcons" ) { buildProofWithCut( ehs1, prover ) }

      val pruned_proof = metrics.time( "cleanproof" ) { CleanStructuralRules( proof.get ) }

      ( pruned_proof, ehs1, lcomp( cutFormulas.head ), lcomp( ehs1.cutFormulas.head ) )
    }

    // Sort the list by size of proofs
    val sorted = proofs.sortWith( ( p1, p2 ) => rulesNumber( p1._1 ) < rulesNumber( p2._1 ) )
    val smallestProof = sorted.head._1
    val ehs = sorted.head._2

    metrics.value( "cuts_in", getStatistics( smallestProof ).cuts )
    metrics.value( "can_sol", sorted.head._3 )
    metrics.value( "min_sol", sorted.head._4 )
    metrics.value( "inf_output", rulesNumber( smallestProof ) )
    metrics.value( "quant_output", quantRulesNumber( smallestProof ) )
    if ( verbose ) println( "\nMinimized cut formula: " + ehs.cutFormulas.head + "\n" )

    if ( verbose ) {
      //      print_log_tuple( tuple );
    }

    Some( smallestProof )
  }

  // MaxSat methods
  private def execute( proof: LKProof, n: Int, timeout: Int, verbose: Boolean ): Option[LKProof] = {

    val clean_proof = CleanStructuralRules( proof )
    val num_rules = rulesNumber( clean_proof )
    val ep = LKToExpansionProof( clean_proof )
    val hasEquality = containsEqualityReasoning( clean_proof )
    execute( ep, hasEquality, num_rules, n, timeout, verbose )
  }

  private def execute( ep: ExpansionSequent, hasEquality: Boolean, num_lk_rules: Int, n: Int, timeout: Int, verbose: Boolean ): Option[LKProof] = {

    val prover = hasEquality match {
      case true  => new EquationalProver()
      case false => new BasicProver()
    }
    val maxsatsolver = new QMaxSAT()

    metrics.value( "quant_input", quantRulesNumberET( ep ) )
    metrics.value( "inf_input", num_lk_rules )

    val endSequent = toShallow( ep )
    if ( verbose ) println( "\nEnd sequent: " + endSequent )

    /** ******** Terms Extraction **********/
    val termset = metrics.time( "termset" ) {
      TermsExtraction( ep )
    }

    val termsetSize = termset.set.size
    metrics.value( "termset", termsetSize )
    if ( verbose ) println( "Size of term set: " + termset.set.size )

    /** ******** Grammar finding **********/
    val grammar = metrics.time( "grammar" ) {
      findMinimalGrammar( termset.set, n, maxsatsolver ) match {
        case g if g.productions.exists( _._1 != g.axiom ) =>
          simpleToMultiGrammar( termset.encoding, g.toVectTratGrammar )
        case _ =>
          throw new CutIntroUncompressibleException( "Found minimal grammar that consists only of tau-productions." )
      }
    }

    /********** Proof Construction **********/

    // For the maxsat method, the number of eigenvariables in the grammar is
    // equivalent to the number of cuts in the final proof, since each cut has
    // only one quantifier.
    metrics.value( "cuts_in", grammar.numVars )
    metrics.value( "mingrammar", grammar.size )
    if ( verbose ) println( "Smallest grammar-size: " + grammar.size )

    val cutFormulas = metrics.time( "sol" ) { computeCanonicalSolutions( grammar ) }
    // Average size of the cut-formula
    val canonicalSolutionSize = ( cutFormulas.foldLeft( 0 )( ( acc, f ) => lcomp( f ) + acc ) ) / cutFormulas.length
    metrics.value( "can_sol", canonicalSolutionSize )
    if ( verbose ) {
      println( "Cut formulas found: " )
      cutFormulas.foreach( f => println( f + "\n" ) )
    }

    // Build the proof only if introducing one cut
    // TODO: implement proof construction for multiple cuts
    //        if ( cutFormulas.length == 1 ) {

    val ehs = new ExtendedHerbrandSequent( endSequent, grammar, cutFormulas )

    val proof = metrics.time( "prcons" ) { buildProofWithCut( ehs, prover ) }

    val pruned_proof = metrics.time( "cleanproof" ) { CleanStructuralRules( proof.get ) }

    metrics.value( "inf_output", rulesNumber( pruned_proof ) )
    metrics.value( "quant_output", quantRulesNumber( pruned_proof ) )

    if ( verbose ) {
      //      print_log_tuple( tuple );
    }

    Some( pruned_proof )
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
            val freeVars = freeVariables( termlist ).toList

            // TODO: try to reverse the variable bindings
            // in the construction of
            if ( freeVars.intersect( variables ).nonEmpty ) {
              val i_f = instantiate( formula, termlist )
              val f = formula match {
                case Ex( _ )  => Neg( i_f )
                case All( _ ) => i_f
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
            val subst = FOLSubstitution( variables.zip( terms ) )
            subst( ci ) :: acc
        }
        val ci_quant = All.Block( variables, ci )
        And( forms ) :: ci_quant :: cut_formulas.tail
      // The last term set contains only constants, so we drop the formula generated with it.
    }.tail.reverse
  }

  private def getCutImpl( cf: FOLFormula, alpha: List[FOLVar], ts: List[List[FOLTerm]] ) = {
    val ant = instantiate( cf, alpha )
    val succ = And( ts.map( termlist => instantiate( cf, termlist ) ).toList )
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
      case All( _ ) => true
      case _        => false
    },
      endSequent.succedent.filter {
        case Ex( _ ) => true
        case _       => false
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
        val termlistlist = grammar.us.getOrElse( f, List() )
        termlistlist.filter( termlist => freeVariables( termlist ).toList.intersect( alphas.take( i ).flatMap( x => x ) ).isEmpty )
      } ) )

    val Uleft = getUs( F.antecedent.asInstanceOf[Seq[FOLFormula]] )
    val Uright = getUs( F.succedent.asInstanceOf[Seq[FOLFormula]] )

    trace( "Uleft : " + Uleft )
    trace( "Uright : " + Uright )

    // define the A_i
    val A: List[FOLFormula] = ( cutFormulas zip alphas ).map {
      case ( cf, ev ) => {
        trace( "computing A" )
        trace( "instantiating " + cf + " with " + ev )
        instantiate( cf, ev )
      }
    }

    trace( "A: " + A )

    // define the sequent corresponding to F[x \ U_i]
    val FU = ( 0 to alphas.size ).map( i => FSequent(
      ( F.antecedent zip Uleft( i ) ).flatMap { case ( f, terms ) => instantiate( f.asInstanceOf[FOLFormula], terms ) },
      ( F.succedent zip Uright( i ) ).flatMap { case ( f, terms ) => instantiate( f.asInstanceOf[FOLFormula], terms ) } ) )

    trace( "FU: " + FU )

    // define A_i[x \ S_i]
    val AS = ( 0 to alphas.size - 1 ).map( i => grammar.ss( i )._2.map( s => instantiate( cutFormulas( i ), s ) ) )

    trace( "AS: " + AS )

    // define the CI_i
    val cutImplications = ( 0 to alphas.size - 1 ).map( i => getCutImpl( cutFormulas( i ), alphas( i ), grammar.ss( i )._2 ) )

    // compute the A_i' via interpolation
    // TODO: increase performance by feeding existing proofs to the
    // interpolation algorithm?
    val Aprime = ( 1 to alphas.size ).reverse.foldLeft( Nil: List[FOLFormula] ) {
      case ( acc, i ) => {
        trace( "A_" + i + ": " + A( i - 1 ) )
        trace( "freeVariables( A( " + i + "  ) ): " + freeVariables( A( i - 1 ) ).toList )
        trace( "alphas.drop( " + i + " ): " + alphas.drop( i - 1 ) )
        // if A_i fulfills the variable condition, set A_i':= A_i
        if ( freeVariables( A( i - 1 ) ) subsetOf alphas.drop( i - 1 ).flatMap( x => x ).toSet ) {
          trace( "fulfills the variable condition" )
          acc :+ A( i - 1 )
        } else // otherwise, compute interpolant I and set A_':= And( A_i, I )
        {
          trace( "does not fulfill the variable condition" )
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
      }
    }.reverse

    val cutFormulasPrime = ( Aprime zip Aprime.indices ).map { case ( a, i ) => All.Block( alphas( i ), a ) }

    // define A'_i[x \ S_i]
    val AprimeS = ( 0 to alphas.size - 1 ).map( i => grammar.ss( i )._2.map( s => instantiate( cutFormulasPrime( i ), s ) ) )

    // define L_1
    val L1 = FSequent( ehs.antecedent ++ ehs.antecedent_alpha, Aprime ++ ehs.succedent ++ ehs.succedent_alpha )

    trace( "L1: " + L1 )

    // define the R_i
    val R = ( 0 to alphas.size - 1 ).map( i =>
      FSequent( AprimeS( i ).toSeq ++ ehs.prop_l, Aprime.drop( i + 1 ) ++ ehs.prop_r ).compose(
        FU( i + 1 ) ) )

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
      val right = buildRightPart( Rproofs_( i ), cutFormulasPrime( i ), grammar.ss( i )._2 )
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
  private def buildLeftPart( i: Int, es: FSequent, A: Seq[FOLFormula], Uleft: Seq[Seq[Seq[Seq[FOLTerm]]]], Uright: Seq[Seq[Seq[Seq[FOLTerm]]]], alphas: Seq[Seq[FOLVar]], cf: FOLFormula, proof: LKProof ) =
    {
      trace( "in buildLeftPart" )
      trace( "Uleft( " + i + " ): " + Uleft( i ) )
      trace( "Uleft( " + ( i + 1 ) + " ): " + Uleft( i + 1 ) )
      trace( "es: " + proof.root )
      def myWeakQuantRules( proof: LKProof, fs: Seq[FOLFormula], instances: Seq[Tuple2[Seq[Seq[FOLTerm]], Seq[Seq[FOLTerm]]]] ) =
        ( fs zip instances ).foldLeft( proof ) {
          case ( proof, ( f, ( ui, uip ) ) ) => {
            trace( "in myWeakQuantRules" )
            trace( "f: " + f )
            trace( "ui: " + ui )
            trace( "uip: " + uip )
            trace( "ui diff uip: " + ( ui diff uip ) )
            genWeakQuantRules( f, ui diff uip, proof )
          }
        }

      val p1 = myWeakQuantRules( proof, es.antecedent.asInstanceOf[Seq[FOLFormula]], Uleft( i ) zip Uleft( i + 1 ) )
      val p2 = myWeakQuantRules( p1, es.succedent.asInstanceOf[Seq[FOLFormula]], Uright( i ) zip Uright( i + 1 ) )

      ForallRightBlock( p2, cf, alphas( i ) )
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
  private def buildRightPart( proof: LKProof, a: FOLFormula, s: Seq[Seq[FOLTerm]] ) =
    {
      trace( "calling buildRightPart" )
      trace( "a: " + a )
      trace( "s: " + s )
      genWeakQuantRules( a, s, proof )
    }

  //TODO: This should be replaced by the proofFromInstances macro rule.
  // Both methods below are responsible for generating the instances of 
  // end-sequent ancestors with the terms from the set U
  def genWeakQuantRules( f: FOLFormula, lst: Seq[Seq[FOLTerm]], ax: LKProof ): LKProof = {
    trace( "calling genWeakQuantRules" )
    trace( "f: " + f )
    trace( "lst: " + lst )
    ( f, lst ) match {
      case ( _, Nil ) => ax
      case ( All( _, _ ), h :: t ) =>
        val newForm = instantiate( f, h )
        ContractionLeftRule( ForallLeftBlock( genWeakQuantRules( f, t, ax ), f, h ), f )
      case ( Ex( _, _ ), h :: t ) =>
        val newForm = instantiate( f, h )
        ContractionRightRule( ExistsRightBlock( genWeakQuantRules( f, t, ax ), f, h ), f )
    }
  }
}

