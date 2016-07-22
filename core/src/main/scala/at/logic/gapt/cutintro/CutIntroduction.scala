package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.grammars._
import at.logic.gapt.grammars.reforest.Reforest
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.utils.logging.{ Logger, metrics }
import at.logic.gapt.utils.runProcess

class CutIntroException( msg: String ) extends Exception( msg )
class CutIntroNonCoveringGrammarException( grammar: VectTratGrammar, term: FOLTerm )
  extends CutIntroException( s"Grammar does not cover the following term in the Herbrand set:\n$term\n\n$grammar" )

trait GrammarFindingMethod {
  def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar]
  def name: String
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

case class ExternalReforestMethod( command: Seq[String] = Seq( "reforest" ) ) extends GrammarFindingMethod {
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

  override def name = "reforest_hs"
}

case object ReforestMethod extends GrammarFindingMethod {
  def findGrammars( lang: Set[FOLTerm] ) = {
    var state = Reforest start lang
    state = Reforest full state
    Some( state.toVTRATG )
  }

  def name = "reforest"
}

/**
 * Represents a schematic extended Herbrand sequent.
 *
 * @param us  Formulas of the original end-sequent, together with their instances.
 * @param ss  Instances of the cut-implications.
 */
case class SchematicExtendedHerbrandSequent( us: Sequent[( FOLFormula, Seq[Seq[FOLTerm]] )], ss: Seq[( Seq[FOLVar], Seq[Seq[FOLTerm]] )] ) {
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

  def substitutions = for ( ( evs, insts ) <- ss ) yield insts.map( inst => FOLSubstitution( evs zip inst ) )

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

  /** Instances of the quantified and propositional formulas in the end-sequent. */
  val endSequentInstances = for {
    ( u, instances ) <- us
    instance <- instances
  } yield instantiate( u, instance )

  def esInstancesInScope( i: Int ): FOLSequent = {
    val evsInScope = eigenVariables.drop( i ).flatten.toSet
    endSequentInstances.filter( freeVariables( _ ) subsetOf evsInScope )
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

object sehsToVTRATG {
  def apply( encoding: InstanceTermEncoding, sehs: SchematicExtendedHerbrandSequent ): VectTratGrammar = {
    val freeVars = freeVariables( sehs.us.elements.flatMap { _._2 } ++ sehs.ss.flatMap { _._2 } flatten ) ++ sehs.eigenVariables.flatten
    val axiom = rename( FOLVar( "x" ), freeVars )
    val nonTerminals = sehs.eigenVariables.map( _.toList )
    val instances = for ( ( f, us ) <- sehs.us; u <- us ) yield instantiate( f, u )
    val productionsFromAx = for ( t <- encoding encode instances ) yield List( axiom ) -> List( t.asInstanceOf[FOLTerm] )
    val otherProds = for ( ( ev, ss ) <- sehs.ss; s <- ss ) yield ev -> s
    val productions = productionsFromAx ++ otherProds

    val grounding = FOLSubstitution( freeVariables( productions flatMap { _._2 } ) diff nonTerminals.flatten.toSet map {
      case FOLVar( n ) => FOLVar( n ) -> FOLConst( n )
    } )

    VectTratGrammar( axiom, List( axiom ) +: nonTerminals, productions map { p => p._1.toList -> grounding( p._2 ).toList } )
  }
}

/**
 * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
 * In practice it does happen if the method used for searching a proof covers a too
 * weak theory (e.g. no equality) or is not complete.
 */
class CutIntroUnprovableException( msg: String ) extends CutIntroException( msg )

object CutIntroduction {

  trait BackgroundTheory {
    def hasEquality: Boolean
    def prover: Prover
  }
  object BackgroundTheory {
    case object Equality extends BackgroundTheory {
      val hasEquality = true
      object prover extends Prover {
        private val smtSolver =
          if ( Z3 isInstalled ) Z3
          else if ( VeriT isInstalled ) VeriT
          else new Escargot( splitting = true, equality = true, propositional = true )

        override def startIncrementalSession() = smtSolver.startIncrementalSession()
        override def isValid( s: HOLSequent ): Boolean = smtSolver isValid s
        override def getLKProof( s: HOLSequent ) = EquationalLKProver getLKProof s
      }
    }
    case object PureFOL extends BackgroundTheory {
      val hasEquality = false
      object prover extends OneShotProver {
        def getLKProof( seq: HOLSequent ) = LKProver getLKProof seq
        override def isValid( seq: HOLSequent ) = Sat4j isValid seq
      }
    }
  }

  def guessBackgroundTheory( sequent: HOLSequent ): BackgroundTheory =
    if ( atoms( sequent ).exists( Eq.unapply( _ ).isDefined ) )
      BackgroundTheory.Equality
    else
      BackgroundTheory.PureFOL

  def guessBackgroundTheory( solutionStructure: SolutionStructure ): BackgroundTheory =
    guessBackgroundTheory( solutionStructure.endSequent )

  def guessBackgroundTheory( expansionProof: ExpansionProof ): BackgroundTheory =
    guessBackgroundTheory( expansionProof.shallow )

  def guessBackgroundTheory( lk: LKProof ): BackgroundTheory =
    if ( containsEqualityReasoning( lk ) )
      BackgroundTheory.Equality
    else
      BackgroundTheory.PureFOL

  def compressToSolutionStructure(
    ep:               ExpansionProof,
    backgroundTheory: BackgroundTheory     = null,
    method:           GrammarFindingMethod = DeltaTableMethod(),
    verbose:          Boolean              = false
  ): Option[SolutionStructure] = {
    if ( backgroundTheory == null )
      return compressToSolutionStructure( ep, guessBackgroundTheory( ep ), method, verbose )

    require(
      isFOLPrenexSigma1( ep.shallow ),
      "Cut-introduction requires first-order prenex end-sequents without strong quantifiers"
    )

    val herbrandSequent = extractInstances( ep )
    val herbrandSequentProof = backgroundTheory.prover.getLKProof( herbrandSequent ).getOrElse {
      throw new CutIntroUnprovableException( "Cannot prove Herbrand sequent." )
    }
    metrics.value( "hs_lcomp", herbrandSequent.elements.map( lcomp( _ ) ).sum )
    metrics.value( "hs_scomp", expressionSize( herbrandSequent.toDisjunction ) )
    metrics.value( "hs_lkinf", herbrandSequentProof.treeLike.size )

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
    }.orElse {
      if ( verbose ) println( "No grammar found." )
      None
    }.flatMap { vtratGrammar =>
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

      val canonicalSS = SolutionStructure( grammar, computeCanonicalSolution( grammar ) )
      require( canonicalSS.isValid( backgroundTheory.prover ) )

      val minimizedSS = metrics.time( "minsol" ) { improveSolutionLK( canonicalSS, backgroundTheory.prover, backgroundTheory.hasEquality ) }
      if ( verbose ) for ( ( cf, i ) <- minimizedSS.formulas.zipWithIndex ) {
        println( s"CNF of minimized cut-formula number $i:" )
        for ( clause <- CNFp( cf ) )
          println( s"  $clause" )
      }
      require( minimizedSS.isValid( backgroundTheory.prover ) )

      val beautifiedSS = metrics.time( "beausol" ) { beautifySolution( minimizedSS ) }
      require( beautifiedSS.isValid( backgroundTheory.prover ) )

      def solStructMetrics( solStruct: SolutionStructure, name: String ) = {
        metrics.value( s"${name}sol_lcomp", solStruct.formulas.map( lcomp( _ ) ).sum )
        metrics.value( s"${name}sol_scomp", solStruct.formulas.map( expressionSize( _ ) ).sum )
        metrics.value( s"${name}sol_nclauses", solStruct.formulas.map( f => CNFp( f ).size ).sum )
        val clauseSizes = solStruct.formulas.flatMap( CNFp.apply ).map( _.size )
        metrics.value( s"${name}sol_maxclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.max )
        metrics.value( s"${name}sol_avgclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.sum.toFloat / clauseSizes.size )
      }
      solStructMetrics( canonicalSS, "can" )
      solStructMetrics( minimizedSS, "min" )
      solStructMetrics( beautifiedSS, "beau" )

      val lcompCanonicalSol = canonicalSS.formulas.map( lcomp( _ ) ).sum
      val lcompMinSol = minimizedSS.formulas.map( lcomp( _ ) ).sum
      val lcompBeauSol = beautifiedSS.formulas.map( lcomp( _ ) ).sum
      val beauGrammar = sehsToVTRATG( encoding, beautifiedSS.sehs )
      metrics.value( "beaugrammar_size", beauGrammar.size )
      metrics.value( "beaugrammar_scomp", beauGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )
      metrics.value( "beausol", beautifiedSS.formulas.map( _.toString ) )

      if ( beautifiedSS.formulas.nonEmpty ) {
        if ( verbose ) {
          println( s"Beautified grammar of size ${beauGrammar.size}:" )
          println( beauGrammar )
          println( s"Size of the canonical solution: $lcompCanonicalSol" )
          println( s"Size of the minimized solution: $lcompMinSol" )
          println( s"Size of the beautified solution: $lcompBeauSol" )
          for ( ( cf, i ) <- beautifiedSS.formulas.zipWithIndex ) {
            println( s"CNF of beautified cut-formula number $i:" )
            for ( clause <- CNFp( cf ) )
              println( s"  $clause" )
          }
        }

        val ehsSequent = beautifiedSS.getDeep
        val ehsResolutionProof = backgroundTheory.prover.getLKProof( ehsSequent ).getOrElse {
          throw new CutIntroUnprovableException( "Cannot prove extended Herbrand sequent." )
        }
        metrics.value( "ehs_lcomp", ehsSequent.elements.map( lcomp( _ ) ).sum )
        metrics.value( "ehs_scomp", expressionSize( ehsSequent.toDisjunction ) )
        metrics.value( "ehs_lkinf", ehsResolutionProof.treeLike.size )

        Some( beautifiedSS )
      } else {
        if ( verbose ) println( "No non-trivial lemma found." )
        None
      }
    }
  }

  def constructLKProof( solStruct: SolutionStructure, backgroundTheory: BackgroundTheory = null, verbose: Boolean = false ): LKProof = {
    if ( backgroundTheory == null ) return constructLKProof( solStruct, guessBackgroundTheory( solStruct ), verbose )

    val proofWithStructuralRules = metrics.time( "prcons" ) {
      buildProofWithCut( solStruct, backgroundTheory.prover )
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

  def compressToLK( ep: ExpansionProof, backgroundTheory: BackgroundTheory = null, method: GrammarFindingMethod = DeltaTableMethod(), verbose: Boolean = false ): Option[LKProof] = {
    if ( backgroundTheory == null ) return compressToLK( ep, guessBackgroundTheory( ep ), method, verbose )
    compressToSolutionStructure( ep, backgroundTheory, method, verbose ) map { constructLKProof( _, backgroundTheory, verbose ) }
  }

  def compressLKProof( p: LKProof, backgroundTheory: BackgroundTheory = null, method: GrammarFindingMethod = DeltaTableMethod(), verbose: Boolean = false ): Option[LKProof] = {
    if ( backgroundTheory == null ) return compressLKProof( p, guessBackgroundTheory( p ), method, verbose )

    val clean_proof = cleanStructuralRules( p )

    if ( verbose )
      println( s"Total inferences in the input proof: ${rulesNumber( clean_proof )}" )

    val ep = eliminateCutsET( LKToExpansionProof( clean_proof ) )

    compressToLK( ep, backgroundTheory, method, verbose )
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
      for ( idx <- sehs.eigenVariables.indices.toStream )
        yield And( esInstancesPerCut.getOrElse( idx, Seq() ) ++
        ( if ( idx == 0 ) Seq() else sehs.ss( idx - 1 )._2.map { s => FOLSubstitution( sehs.ss( idx - 1 )._1 zip s )( canSol( idx - 1 ) ) } ) )
    canSol.toList
  }

  def buildProofWithCut( solStruct: SolutionStructure, prover: Prover ): LKProof = {
    // ithCut(i) returns a proof that ends in (availableESInstanceFormulas ++ endSequent :+ qfCutFormulas(i+1) :+ ... :+ qfCutFormulas(n))
    def ithCut( i: Int ): LKProof = {
      val eigenVariablesInScope = ( for ( ( evs, j ) <- solStruct.sehs.eigenVariables.zipWithIndex; ev <- evs if i < j ) yield ev ).toSet
      val availableESInstanceFormulas = for ( ( u, insts ) <- solStruct.sehs.us; inst <- insts if freeVariables( inst ) subsetOf eigenVariablesInScope ) yield instantiate( u, inst )
      val availableCutFormulas = for ( ( cf, j ) <- solStruct.formulas.zipWithIndex if i < j ) yield cf
      // Instances of the sequent on the right side of the cut, without the instances of the cut-formula.
      val context = availableESInstanceFormulas :++ availableCutFormulas

      if ( i == -1 ) {
        ContractionMacroRule( prover getLKProof context getOrElse { throw new CutIntroUnprovableException( context.toString ) } )
      } else {
        var lhs = ithCut( i - 1 )
        for {
          ( u, insts ) <- solStruct.sehs.us
          inst <- insts.distinct
          if freeVariables( inst ).intersect( solStruct.sehs.eigenVariables( i ).toSet ).nonEmpty
        } lhs = WeakQuantifierBlock( lhs, u, inst )
        lhs = ForallRightBlock( lhs, solStruct.cutFormulas( i ), solStruct.sehs.eigenVariables( i ) )
        lhs = ContractionMacroRule( lhs )

        val rhsQfSequent = ( for ( inst <- solStruct.sehs.ss( i )._2 ) yield instantiate( solStruct.cutFormulas( i ), inst ) ) ++: context
        var rhs = prover getLKProof rhsQfSequent getOrElse { throw new CutIntroUnprovableException( rhsQfSequent.toString ) }
        rhs = WeakeningContractionMacroRule( rhs, rhsQfSequent, strict = true )
        for ( inst <- solStruct.sehs.ss( i )._2 )
          rhs = ForallLeftBlock( rhs, solStruct.cutFormulas( i ), inst )
        rhs = ContractionMacroRule( rhs )

        ContractionMacroRule( CutRule( lhs, rhs, solStruct.cutFormulas( i ) ) )
      }
    }

    var proof = ithCut( solStruct.formulas.indices.last )
    for {
      ( u, insts ) <- solStruct.sehs.us
      inst <- insts.distinct
      if freeVariables( inst ).isEmpty
    } proof = WeakQuantifierBlock( proof, u, inst )
    WeakeningContractionMacroRule( proof, solStruct.endSequent, strict = true )
  }
}

