/**
 * Cut introduction algorithm
 *
 *
 */
package at.logic.gapt.proofs.lk.cutIntroduction

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.{ findMinimalVectGrammar, VectTratGrammar }
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

trait GrammarFindingMethod {
  def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar]
  def name: String
}

case class DeltaTableMethod( manyQuantifiers: Boolean ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val delta = manyQuantifiers match {
      case true  => new UnboundedVariableDelta()
      case false => new OneVariableDelta()
    }
    val eigenvariable = "α"
    val deltatable = metrics.time( "dtable" ) { new DeltaTable( lang.toList, eigenvariable, delta ) }

    metrics.time( "grammar" ) {
      ComputeGrammars.findValidGrammars( lang.toList, deltatable, eigenvariable ).sortBy( _.size ).headOption
    }
  }

  override def name: String = if ( manyQuantifiers ) "many_dtable" else "1_dtable"
}

case class MaxSATMethod( nonTerminalLengths: Int* ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = metrics.time( "grammar" ) {
    Some( findMinimalVectGrammar( lang.toSeq, nonTerminalLengths, new QMaxSAT ) )
  }

  override def name: String = s"${nonTerminalLengths.mkString( "_" )}_maxsat"
}

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 */
class CutIntroEHSUnprovableException( msg: String ) extends CutIntroException( msg )

object CutIntroduction extends Logger {

  /**
   * Tries to introduce one cut with one quantifier to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   */
  def one_cut_one_quantifier( proof: LKProof, verbose: Boolean ) =
    execute( proof, DeltaTableMethod( false ), verbose )
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
   */
  def one_cut_one_quantifier( es: ExpansionSequent, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, DeltaTableMethod( false ), verbose )

  /**
   * Tries to introduce one cut with as many quantifiers as possible to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A proof with one quantified cut.
   */
  def one_cut_many_quantifiers( proof: LKProof, verbose: Boolean ) =
    execute( proof, DeltaTableMethod( true ), verbose )
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
   */
  def one_cut_many_quantifiers( es: ExpansionSequent, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, DeltaTableMethod( true ), verbose )
  /**
   * Tries to introduce many cuts with one quantifier each to the LKProof.
   *
   * @param proof The proof for introducing a cut.
   * @param numcuts The (maximum) number of cuts to be introduced
   * @param verbose Whether information about the cut-introduction process
   *        should be printed on screen.
   * @return A list of cut-formulas.
   */
  def many_cuts_one_quantifier( proof: LKProof, numcuts: Int, verbose: Boolean ) =
    execute( proof, MaxSATMethod( Seq.fill( numcuts )( 1 ): _* ), verbose )
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
   */
  def many_cuts_one_quantifier( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, MaxSATMethod( Seq.fill( numcuts )( 1 ): _* ), verbose )

  def execute( proof: LKProof, method: GrammarFindingMethod ): Option[LKProof] = execute( proof, method, false )
  def execute( proof: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod ): Option[LKProof] =
    execute( proof, hasEquality, method, false )

  def execute( proof: LKProof, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] = {
    val clean_proof = CleanStructuralRules( proof )
    metrics.value( "inf_input", rulesNumber( clean_proof ) )

    if ( verbose )
      println( s"Total inferences in the input proof: ${rulesNumber( clean_proof )}" )

    val ep = LKToExpansionProof( clean_proof )
    val hasEquality = containsEqualityReasoning( clean_proof )

    execute( ep, hasEquality, method, verbose )
  }

  def execute( ep: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] = {

    val prover = hasEquality match {
      case true  => new EquationalProver()
      case false => new BasicProver()
    }

    metrics.value( "quant_input", quantRulesNumberET( ep ) )

    if ( verbose )
      println( s"Quantifier inferences in the input proof: ${quantRulesNumberET( ep )}" )

    val endSequent = toShallow( ep )
    if ( verbose ) println( s"End sequent: $endSequent" )

    /********** Term set Extraction **********/
    val termset = metrics.time( "termset" ) { TermsExtraction( ep ) }

    metrics.value( "termset", termset.set.size )
    if ( verbose ) println( s"Size of term set: ${termset.set.size}" )

    /********** Grammar finding **********/
    method.findGrammars( termset.set.toSet ).filter { g =>
      g.productions.exists( _._1 != g.axiomVect )
    }.map { vtratGrammar =>

      metrics.value( "grammar_size", vtratGrammar.size )

      if ( verbose ) {
        println( s"Smallest grammar of size ${vtratGrammar.size}:" )
        println( vtratGrammar )
      }

      val grammar = simpleToMultiGrammar( termset.encoding, vtratGrammar )

      /** ******** Proof Construction **********/

      val canonicalEHS = new ExtendedHerbrandSequent( endSequent, grammar, computeCanonicalSolutions( grammar ) )

      val minimizedEHS = metrics.time( "minsol" ) {
        if ( hasEquality && canonicalEHS.cutFormulas.size == 1 )
          MinimizeSolution.applyEq( canonicalEHS, prover )
        else if ( !hasEquality )
          MinimizeSolution.apply( canonicalEHS, prover )
        else
          canonicalEHS // TODO: minimize solution for multiple cuts with equality
      }

      val Some( proofWithStructuralRules ) = metrics.time( "prcons" ) {
        buildProofWithCut( minimizedEHS, prover )
      }

      val proof = metrics.time( "cleanproof" ) {
        CleanStructuralRules( proofWithStructuralRules )
      }

      val lcompCanonicalSol = canonicalEHS.cutFormulas.map( lcomp( _ ) ).sum
      val lcompMinSol = minimizedEHS.cutFormulas.map( lcomp( _ ) ).sum

      metrics.value( "cuts_in", getStatistics( proof ).cuts )
      metrics.value( "can_sol", lcompCanonicalSol )
      metrics.value( "min_sol", lcompMinSol )
      metrics.value( "inf_output", rulesNumber( proof ) )
      metrics.value( "quant_output", quantRulesNumber( proof ) )
      if ( verbose ) {
        println( s"Size of the canonical solution: $lcompCanonicalSol" )
        println( s"Size of the minimized solution: $lcompMinSol" )
        println( "Minimized cut formulas:" )
        minimizedEHS.cutFormulas foreach println
        println( s"Number of cuts introduced: ${getStatistics( proof ).cuts}" )
        println( s"Total inferences in the proof with cut(s): ${rulesNumber( proof )}" )
        println( s"Quantifier inferences in the proof with cut(s): ${quantRulesNumber( proof )}" )
      }

      proof
    } orElse {
      if ( verbose ) println( "No grammar found." )
      None
    }
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
    val quantPart = HOLSequent(
      endSequent.antecedent.filter {
        case All( _ ) => true
        case _        => false
      },
      endSequent.succedent.filter {
        case Ex( _ ) => true
        case _       => false
      }
    )

    // In our setting, we work with a sequent instead of a formula F as in the paper.
    // The following sequent corresponds to that formula.
    val F = HOLSequent( ehs.quant_l, ehs.quant_r )

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
    val FU = ( 0 to alphas.size ).map( i => HOLSequent(
      ( F.antecedent zip Uleft( i ) ).flatMap { case ( f, terms ) => instantiate( f.asInstanceOf[FOLFormula], terms ) },
      ( F.succedent zip Uright( i ) ).flatMap { case ( f, terms ) => instantiate( f.asInstanceOf[FOLFormula], terms ) }
    ) )

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
          val allf = FU( 0 ) compose ( new HOLSequent( ehs.prop_l, ehs.prop_r ) )
          val posf = FU( i - 1 ) compose ( new HOLSequent( ehs.prop_l, ehs.prop_r ) )
          val negf = allf diff posf
          val neg = negf compose ( new HOLSequent( cutImplications.take( i - 1 ), Nil ) )
          val pos = posf compose ( new HOLSequent( AS( i - 1 ), acc ) )
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
    val L1 = HOLSequent( ehs.antecedent ++ ehs.antecedent_alpha, Aprime ++ ehs.succedent ++ ehs.succedent_alpha )

    trace( "L1: " + L1 )

    // define the R_i
    val R = ( 0 to alphas.size - 1 ).map( i =>
      HOLSequent( AprimeS( i ).toSeq ++ ehs.prop_l, Aprime.drop( i + 1 ) ++ ehs.prop_r ).compose(
        FU( i + 1 )
      ) )

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
      val cont2 = ContractionMacroRule( cont1, HOLSequent( ehs.prop_l, ehs.prop_r ), false )
      ContractionMacroRule( cont2, HOLSequent( Nil, Aprime.drop( i + 1 ) ), false )
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
  private def buildLeftPart( i: Int, es: HOLSequent, A: Seq[FOLFormula], Uleft: Seq[Seq[Seq[Seq[FOLTerm]]]], Uright: Seq[Seq[Seq[Seq[FOLTerm]]]], alphas: Seq[Seq[FOLVar]], cf: FOLFormula, proof: LKProof ) =
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

