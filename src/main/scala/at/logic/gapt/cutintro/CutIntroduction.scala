package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansionTrees.{ quantRulesNumber => quantRulesNumberET, _ }
import at.logic.gapt.proofs.lk.ExtractInterpolant
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.resolution.{ simplifyResolutionProof, numberOfResolutionsAndParamodulations }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.basicProver._
import at.logic.gapt.provers.eqProver._
import at.logic.gapt.provers.maxsat.{ bestAvailableMaxSatSolver, MaxSATSolver }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.logging.{ metrics, Logger }

class CutIntroException( msg: String ) extends Exception( msg )
class CutIntroNonCoveringGrammarException( grammar: VectTratGrammar, term: FOLTerm )
  extends CutIntroException( s"Grammar does not cover the following term in the Herbrand set:\n$term\n\n$grammar" )

trait GrammarFindingMethod {
  def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar]
  def name: String
}

case class DeltaTableMethod( manyQuantifiers: Boolean ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
    val delta = manyQuantifiers match {
      case true  => new Deltas.UnboundedVariableDelta()
      case false => new Deltas.OneVariableDelta()
    }
    val eigenvariable = "α"
    val deltatable = metrics.time( "dtable" ) { new DeltaTable( lang.toList, eigenvariable, delta ) }

    metrics.time( "dtable2grammar" ) {
      ComputeGrammars.findValidGrammars( lang.toList, deltatable, eigenvariable ).sortBy( _.size ).headOption
    }
  }

  override def name: String = if ( manyQuantifiers ) "many_dtable" else "1_dtable"
}

case class MaxSATMethod( solver: MaxSATSolver, nonTerminalLengths: Int* ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] =
    Some( findMinimalVectGrammar( lang, nonTerminalLengths, solver ) )

  override def name: String = s"${nonTerminalLengths.mkString( "_" )}_maxsat"
}
object MaxSATMethod {
  def apply( nonTerminalLengths: Int* ): MaxSATMethod =
    MaxSATMethod( bestAvailableMaxSatSolver, nonTerminalLengths: _* )
}

/**
 * Represents a schematic extended Herbrand sequent.
 *
 * @param us  Formulas of the original end-sequent, together with their instances.
 * @param ss  Instances of the cut-implications.
 */
// TODO: make us quantifier-free
case class SchematicExtendedHerbrandSequent( us: Sequent[( FOLFormula, List[List[FOLTerm]] )], ss: List[( List[FOLVar], List[List[FOLTerm]] )] ) {
  require( ss.forall { case ( vars, inst ) => inst.forall { case termlist => vars.length == termlist.length } } )

  us.antecedent foreach {
    case ( All.Block( vs, f ), insts ) =>
      require( !containsQuantifier( f ) )
      for ( i <- insts ) require( i.size == vs.size )
  }
  us.succedent foreach {
    case ( Ex.Block( vs, f ), insts ) =>
      require( !containsQuantifier( f ) )
      for ( i <- insts ) require( i.size == vs.size )
  }

  /** Size of the grammar, i.e. |u| + |s| */
  def size = ( us.elements ++ ss ).map( _._2.size ).sum

  /** Eigenvariables that occur in the seHs. */
  def eigenVariables = ss.map( _._1 )

  /** Number of eigenvariables that occur in this seHs. */
  def numVars = eigenVariables.length

  def language = us map {
    case ( u, uInst ) =>
      var instances = uInst
      ss foreach {
        case ( sVars, sInstances ) =>
          instances = for ( instance <- instances; sInstance <- sInstances )
            yield FOLSubstitution( sVars zip sInstance )( instance ).toList
      }
      u -> instances
  }

  override def toString: String = {
    val out = new StringBuilder
    out append s"U:\n"
    for ( ( f, insts ) <- us ) {
      out append s"  $f:\n"
      for ( inst <- insts ) out append s"    $inst\n"
    }
    out append s"S:\n"
    for ( ( v, insts ) <- ss ) {
      out append s"  $v:\n"
      for ( inst <- insts ) out append s"    $inst\n"
    }
    out.result()
  }
}

object vtratgToSEHS {
  def apply( encoding: InstanceTermEncoding, g: VectTratGrammar ): SchematicExtendedHerbrandSequent = {
    val us = encoding.endSequent zip encoding.symbols map {
      case ( u: FOLFormula, sym ) =>
        u -> g.rightHandSides( g.axiomVect ).map( _.head ).toList.
          collect { case Apps( `sym`, args ) => args map { _.asInstanceOf[FOLTerm] } }
    }
    val slist = g.nonTerminals.filter( _ != g.axiomVect ).
      map { a => a -> g.rightHandSides( a ).toList }.
      filter( _._2.nonEmpty ).toList

    SchematicExtendedHerbrandSequent( us, slist )
  }
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
  @deprecated( "Use compressLKProof instead", "2015-09-03" )
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
  @deprecated( "Use compressToLK instead", "2015-09-03" )
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
  @deprecated( "Use compressLKProof instead", "2015-09-03" )
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
  @deprecated( "Use compressToLK instead", "2015-09-03" )
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
  @deprecated( "Use compressLKProof instead", "2015-09-03" )
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
  @deprecated( "Use compressToLK instead", "2015-09-03" )
  def many_cuts_one_quantifier( es: ExpansionSequent, numcuts: Int, hasEquality: Boolean, verbose: Boolean ) =
    execute( es, hasEquality, MaxSATMethod( Seq.fill( numcuts )( 1 ): _* ), verbose )

  @deprecated( "Use compressLKProof instead", "2015-09-03" )
  def execute( proof: LKProof, method: GrammarFindingMethod ): Option[LKProof] = execute( proof, method, false )
  @deprecated( "Use compressToLK instead", "2015-09-03" )
  def execute( proof: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod ): Option[LKProof] =
    execute( proof, hasEquality, method, false )

  @deprecated( "Use compressLKProof instead", "2015-09-03" )
  def execute( proof: LKProof, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] =
    compressLKProof( proof, method, verbose )

  @deprecated( "Use compressToLK instead", "2015-09-03" )
  def execute( ep: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] =
    compressToLK( ep, hasEquality, method, verbose )

  def compressToEHS( ep: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[ExtendedHerbrandSequent] = {

    val prover = if ( hasEquality ) EquationalProver else BasicProver

    val herbrandSequent = extractInstances( ep )
    val Some( herbrandSequentResolutionProof ) = Prover9.getRobinsonProof( herbrandSequent )
    metrics.value( "hs_lcomp", herbrandSequent.elements.map( lcomp( _ ) ).sum )
    metrics.value( "hs_scomp", expressionSize( herbrandSequent.toFormula ) )
    metrics.value( "hs_resinf", numberOfResolutionsAndParamodulations( simplifyResolutionProof( herbrandSequentResolutionProof ) ) )

    metrics.value( "quant_input", quantRulesNumberET( ep ) )

    if ( verbose )
      println( s"Quantifier inferences in the input proof: ${quantRulesNumberET( ep )}" )

    val endSequent = toShallow( ep )
    if ( verbose ) println( s"End sequent: $endSequent" )

    /********** Term set Extraction **********/
    val encoding = FOLInstanceTermEncoding( endSequent )
    val termset = groundTerms( encoding encode ep ) map { _.asInstanceOf[FOLTerm] }

    metrics.value( "termset", termset.size )
    metrics.value( "termset_scomp", termset.toSeq map { expressionSize( _ ) } sum )
    metrics.value( "termset_trivial", termset.size == termset.map { case FOLFunction( r, _ ) => r }.size )
    if ( verbose ) println( s"Size of term set: ${termset.size}" )

    /********** Grammar finding **********/
    metrics.time( "grammar" ) {
      method.findGrammars( termset )
    }.filter { g =>
      g.productions.exists( _._1 != g.axiomVect )
    }.map { vtratGrammar =>

      val generatedLanguage = vtratGrammar.language
      metrics.value( "grammar_lang_size", generatedLanguage.size )
      termset foreach { term =>
        if ( !( generatedLanguage contains term ) )
          throw new CutIntroNonCoveringGrammarException( vtratGrammar, term )
      }

      metrics.value( "grammar_size", vtratGrammar.size )
      metrics.value( "grammar_scomp", vtratGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )

      if ( verbose ) {
        println( s"Smallest grammar of size ${vtratGrammar.size}:" )
        println( vtratGrammar )
      }

      val grammar = vtratgToSEHS( encoding, vtratGrammar )

      val canonicalEHS = ExtendedHerbrandSequent( grammar, computeCanonicalSolution( grammar ) )

      val minimizedEHS = metrics.time( "minsol" ) { improveSolutionLK( canonicalEHS, prover, hasEquality ) }

      val lcompCanonicalSol = canonicalEHS.cutFormulas.map( lcomp( _ ) ).sum
      val lcompMinSol = minimizedEHS.cutFormulas.map( lcomp( _ ) ).sum

      metrics.value( "cansol_lcomp", lcompCanonicalSol )
      metrics.value( "minsol_lcomp", lcompMinSol )
      metrics.value( "cansol_scomp", canonicalEHS.cutFormulas.map( expressionSize( _ ) ).sum )
      metrics.value( "minsol_scomp", minimizedEHS.cutFormulas.map( expressionSize( _ ) ).sum )
      metrics.value( "minsol", minimizedEHS.cutFormulas.map( _.toString ) )
      if ( verbose ) {
        println( s"Size of the canonical solution: $lcompCanonicalSol" )
        println( s"Size of the minimized solution: $lcompMinSol" )
        println( "Minimized cut formulas:" )
        minimizedEHS.cutFormulas foreach println
      }

      val ehsSequent = minimizedEHS.getDeep
      val Some( ehsResolutionProof ) = Prover9.getRobinsonProof( ehsSequent )
      metrics.value( "ehs_lcomp", ehsSequent.elements.map( lcomp( _ ) ).sum )
      metrics.value( "ehs_scomp", expressionSize( ehsSequent.toFormula ) )
      metrics.value( "ehs_resinf", numberOfResolutionsAndParamodulations( simplifyResolutionProof( ehsResolutionProof ) ) )

      minimizedEHS
    } orElse {
      if ( verbose ) println( "No grammar found." )
      None
    }
  }

  def constructLKProof( ehs: ExtendedHerbrandSequent, hasEquality: Boolean, verbose: Boolean = false ): LKProof = {
    val prover = if ( hasEquality ) EquationalProver else BasicProver

    val Some( proofWithStructuralRules ) = metrics.time( "prcons" ) {
      buildProofWithCut( ehs, prover )
    }

    val proof = metrics.time( "cleanproof" ) {
      cleanStructuralRules( proofWithStructuralRules )
    }

    metrics.value( "lkcuts_output", cutsNumber( proof ) )
    metrics.value( "lkinf_output", rulesNumber( proof ) )
    metrics.value( "lkquant_output", quantRulesNumber( proof ) )
    if ( verbose ) {
      println( s"Number of cuts introduced: ${cutsNumber( proof )}" )
      println( s"Total inferences in the proof with cut(s): ${rulesNumber( proof )}" )
      println( s"Quantifier inferences in the proof with cut(s): ${quantRulesNumber( proof )}" )
    }

    proof
  }

  def compressToLK( ep: ExpansionSequent, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] =
    compressToEHS( ep, hasEquality, method, verbose ) map { constructLKProof( _, hasEquality, verbose ) }

  def compressLKProof( p: LKProof, method: GrammarFindingMethod = DeltaTableMethod( manyQuantifiers = false ), verbose: Boolean = false ): Option[LKProof] = {
    val clean_proof = cleanStructuralRules( p )

    if ( verbose )
      println( s"Total inferences in the input proof: ${rulesNumber( clean_proof )}" )

    val ep = LKToExpansionProof( clean_proof )
    val hasEquality = containsEqualityReasoning( clean_proof )

    compressToLK( ep, hasEquality, method, verbose )
  }

  /**
   * Computes the modified canonical solution, where instances of
   * formulas in the end-sequent are introduced as late as possible.
   */
  def computeCanonicalSolution( sehs: SchematicExtendedHerbrandSequent ): List[FOLFormula] = {
    val eigenVarIdx = ( for ( ( evs, i ) <- sehs.eigenVariables.zipWithIndex; ev <- evs ) yield ev -> i ).toMap
    val esInstances = for ( ( u, is ) <- sehs.us; i <- is ) yield instantiate( u, i )
    val esInstancesPerCut = esInstances.map( identity, -_ ).elements.
      groupBy { freeVariables( _ ).collect( eigenVarIdx ).union( Set( sehs.eigenVariables.size ) ).min }
    lazy val canSol: Stream[FOLFormula] =
      for ( ( evs, idx ) <- sehs.eigenVariables.zipWithIndex.toStream )
        yield All.Block( evs, And( esInstancesPerCut.getOrElse( idx, Seq() ) ++
        ( if ( idx == 0 ) Seq() else sehs.ss( idx - 1 )._2.map { instantiate( canSol( idx - 1 ), _ ) } ) ) )
    canSol.toList
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
    val grammar = ehs.sehs

    trace( "grammar: " + grammar )
    trace( "cutFormulas: " + cutFormulas )

    val alphas = grammar.eigenVariables

    // As an efficiency improvement, we treat the non-quantified part of the end-sequent
    // separately (since it never needs to be instantiated).
    val quantPart = HOLSequent(
      endSequent.antecedent.filter {
        case All( _, _ ) => true
        case _           => false
      },
      endSequent.succedent.filter {
        case Ex( _, _ ) => true
        case _          => false
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
        val termlistlist = grammar.us.elements.find( _._1 == f ).map( _._2 ).getOrElse( List() )
        termlistlist.filter( termlist => freeVariables( termlist ).toList.intersect( alphas.take( i ).flatMap( x => x ) ).isEmpty )
      } ) )

    val Uleft = getUs( F.antecedent.asInstanceOf[Seq[FOLFormula]] )
    val Uright = getUs( F.succedent.asInstanceOf[Seq[FOLFormula]] )

    trace( "Uleft : " + Uleft )
    trace( "Uright : " + Uright )

    // define the A_i
    val A: List[FOLFormula] = ( cutFormulas.toList zip alphas ).map {
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

    val cutFormulasPrime = A.zipWithIndex.map { case ( a, i ) => All.Block( alphas( i ), a ) }

    // define A'_i[x \ S_i]
    val AprimeS = ( 0 to alphas.size - 1 ).map( i => grammar.ss( i )._2.map( s => instantiate( cutFormulasPrime( i ), s ) ) )

    // define L_1
    val L1 = HOLSequent( ehs.antecedent ++ ehs.antecedent_alpha, A ++ ehs.succedent ++ ehs.succedent_alpha )

    trace( "L1: " + L1 )

    // define the R_i
    val R = ( 0 to alphas.size - 1 ).map( i =>
      HOLSequent( AprimeS( i ).toSeq ++ ehs.prop_l, A.drop( i + 1 ) ++ ehs.prop_r ).compose(
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
      val left = buildLeftPart( i, quantPart, A, Uleft, Uright, alphas, cutFormulasPrime( i ), lproof )
      val right = buildRightPart( Rproofs_( i ), cutFormulasPrime( i ), grammar.ss( i )._2 )
      val cut = CutRule( left, right, cutFormulasPrime( i ) )
      val cont1 = ContractionMacroRule( cut, FU( i + 1 ), false )
      val cont2 = ContractionMacroRule( cont1, HOLSequent( ehs.prop_l, ehs.prop_r ), false )
      ContractionMacroRule( cont2, HOLSequent( Nil, A.drop( i + 1 ) ), false )
    } )

    def finish( p: LKProof, fs: Seq[FOLFormula], instances: Seq[Seq[Seq[FOLTerm]]] ) =
      ( fs zip instances ).foldLeft( p ) { case ( proof, ( f, is ) ) => genWeakQuantRules( f, is, proof ) }

    val proof_ = finish( proof, quantPart.antecedent.asInstanceOf[Seq[FOLFormula]], Uleft( alphas.size ) )
    val proof__ = finish( proof_, quantPart.succedent.asInstanceOf[Seq[FOLFormula]], Uright( alphas.size ) )

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
      def myWeakQuantRules( proof: LKProof, fs: Seq[FOLFormula], instances: Seq[Tuple2[Seq[Seq[FOLTerm]], Seq[Seq[FOLTerm]]]] ) =
        ( fs zip instances ).foldLeft( proof ) {
          case ( proof, ( f, ( ui, uip ) ) ) => {
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

