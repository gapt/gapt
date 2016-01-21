package at.logic.gapt.cutintro

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.grammars._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolution.{ simplifyResolutionProof, numberOfResolutionsAndParamodulations }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.basicProver._
import at.logic.gapt.provers.eqProver._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.maxsat.{ bestAvailableMaxSatSolver, MaxSATSolver }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.logging.{ metrics, Logger }
import at.logic.gapt.utils.runProcess

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

case class ReforestMethod( command: Seq[String] = Seq( "reforest" ) ) extends GrammarFindingMethod {
  def findRecSchem( lang: Set[FOLTerm] ): RecursionScheme = {
    val renaming = for ( ( c, i ) <- constants( lang ).zipWithIndex ) yield c -> FOLFunctionConst( s"f$i", arity( c.exptype ) )

    def toReforestInput( term: LambdaExpression ): String = term match {
      case FOLFunction( f, Seq() ) => f
      case FOLFunction( f, as )    => s"$f(${as map toReforestInput mkString ","})"
    }

    val input = lang map { TermReplacement( _, renaming.toMap[LambdaExpression, LambdaExpression] ) } map toReforestInput mkString "\n"
    val output = runProcess( command, input )

    import Prover9TermParserLadrStyle.parseTerm
    val back = renaming.map { _.swap }.toMap[LambdaExpression, LambdaExpression]
    val rules = output split "\n" map { line =>
      val Array( lhs, rhs ) = line split "->"
      Rule( parseTerm( lhs ), TermReplacement( parseTerm( rhs ), back ) )
    }
    RecursionScheme( FOLConst( "A0" ), rules toSet )
  }

  override def findGrammars( lang: Set[FOLTerm] ) =
    Some( recSchemToVTRATG( findRecSchem( lang ) ) )

  override def name = "reforest"
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

  def compressToEHS( ep: ExpansionProof, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[ExtendedHerbrandSequent] = {
    require(
      isFOLPrenexSigma1( ep.shallow ),
      "Cut-introduction requires first-order prenex end-sequents without strong quantifiers"
    )

    val prover = if ( hasEquality ) EquationalProver else BasicProver
    val resProver = if ( Prover9 isInstalled ) Prover9 else Escargot

    val herbrandSequent = extractInstances( ep )
    val herbrandSequentResolutionProof = resProver getRobinsonProof herbrandSequent getOrElse {
      throw new CutIntroEHSUnprovableException( s"Cannot prove Herbrand sequent using ${resProver.getClass.getSimpleName}." )
    }
    metrics.value( "hs_lcomp", herbrandSequent.elements.map( lcomp( _ ) ).sum )
    metrics.value( "hs_scomp", expressionSize( herbrandSequent.toFormula ) )
    metrics.value( "hs_resinf", numberOfResolutionsAndParamodulations( simplifyResolutionProof( herbrandSequentResolutionProof ) ) )

    metrics.value( "quant_input", numberOfInstancesET( ep.expansionSequent ) )

    if ( verbose )
      println( s"Quantifier inferences in the input proof: ${numberOfInstancesET( ep.expansionSequent )}" )

    val endSequent = ep.shallow
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
        for ( ( cf, i ) <- minimizedEHS.cutFormulas.zipWithIndex ) {
          println( s"CNF of minimized cut-formula number $i:" )
          for ( clause <- CNFp toClauseList cf )
            println( s"  $clause" )
        }
      }

      val ehsSequent = minimizedEHS.getDeep
      val ehsResolutionProof = resProver getRobinsonProof ehsSequent getOrElse {
        throw new CutIntroEHSUnprovableException( s"Cannot prove extended Herbrand sequent using ${resProver.getClass.getSimpleName}." )
      }
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

    val proofWithStructuralRules = metrics.time( "prcons" ) {
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

  def compressToLK( ep: ExpansionProof, hasEquality: Boolean, method: GrammarFindingMethod, verbose: Boolean ): Option[LKProof] =
    compressToEHS( ep, hasEquality, method, verbose ) map { constructLKProof( _, hasEquality, verbose ) }

  def compressLKProof( p: LKProof, method: GrammarFindingMethod = DeltaTableMethod( manyQuantifiers = false ), verbose: Boolean = false ): Option[LKProof] = {
    val clean_proof = cleanStructuralRules( p )

    if ( verbose )
      println( s"Total inferences in the input proof: ${rulesNumber( clean_proof )}" )

    val ep = eliminateCutsET( LKToExpansionProof( clean_proof ) )
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

  def buildProofWithCut( ehs: ExtendedHerbrandSequent, prover: Prover ): LKProof = {
    val qfCutFormulas = for ( ( cf, ( evs, _ ) ) <- ehs.cutFormulas zip ehs.sehs.ss ) yield instantiate( cf, evs )

    // ithCut(i) returns a proof that ends in (endSequent :+ qfCutFormulas(i+1) :+ ... :+ qfCutFormulas(n))
    def ithCut( i: Int ): LKProof = {
      val eigenVariablesInScope = ( for ( ( evs, j ) <- ehs.sehs.eigenVariables.zipWithIndex; ev <- evs if i < j ) yield ev ).toSet
      val availableESInstances = for ( ( u, insts ) <- ehs.sehs.us; inst <- insts if freeVariables( inst ) subsetOf eigenVariablesInScope ) yield ( u, inst )
      val availableESInstanceFormulas = for ( ( u, inst ) <- availableESInstances ) yield instantiate( u, inst )
      val availableCutFormulas = for ( ( cf, j ) <- qfCutFormulas.zipWithIndex if i < j ) yield cf
      // Instances of the sequent on the right side of the cut, without the instances of the cut-formula.
      val context = availableESInstanceFormulas :++ availableCutFormulas

      if ( i == -1 ) {
        var proof = prover getLKProof context getOrElse { throw new CutIntroEHSUnprovableException( context.toString ) }
        proof = WeakeningContractionMacroRule( proof, context, strict = true )
        for ( ( u, inst ) <- availableESInstances.antecedent )
          proof = ForallLeftBlock( proof, u, inst )
        for ( ( u, inst ) <- availableESInstances.succedent )
          proof = ExistsRightBlock( proof, u, inst )

        ContractionMacroRule( proof )
      } else {
        val lhs = ForallRightBlock( ithCut( i - 1 ), ehs.cutFormulas( i ), ehs.sehs.ss( i )._1 )

        val rhsQfSequent = ( for ( inst <- ehs.sehs.ss( i )._2 ) yield instantiate( ehs.cutFormulas( i ), inst ) ) ++: context
        var rhs = prover getLKProof rhsQfSequent getOrElse { throw new CutIntroEHSUnprovableException( rhsQfSequent.toString ) }
        rhs = WeakeningContractionMacroRule( rhs, rhsQfSequent, strict = true )
        for ( ( u, inst ) <- availableESInstances.antecedent )
          rhs = ForallLeftBlock( rhs, u, inst )
        for ( ( u, inst ) <- availableESInstances.succedent )
          rhs = ExistsRightBlock( rhs, u, inst )
        for ( inst <- ehs.sehs.ss( i )._2 )
          rhs = ForallLeftBlock( rhs, ehs.cutFormulas( i ), inst )
        rhs = ContractionMacroRule( rhs )

        ContractionMacroRule( CutRule( lhs, rhs, ehs.cutFormulas( i ) ) )
      }
    }

    ithCut( ehs.cutFormulas.indices.last )
  }
}

