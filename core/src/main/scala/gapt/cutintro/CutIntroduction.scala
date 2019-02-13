package gapt.cutintro

import gapt.expr._
import gapt.expr.fol.{ isFOLPrenexSigma1, isPrenexSigma1 }
import gapt.expr.hol._
import gapt.expr.util.expressionSize
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.grammars._
import gapt.grammars.reforest.Reforest
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion._
import gapt.proofs.lk._
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.cleanStructuralRules
import gapt.proofs.lk.util.EquationalLKProver
import gapt.proofs.lk.util.LKProver
import gapt.proofs.lk.util.containsEqualityReasoning
import gapt.proofs.lk.util.cutsNumber
import gapt.proofs.lk.util.quantRulesNumber
import gapt.proofs.lk.util.rulesNumber
import gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning }
import gapt.provers.Session.Session
import gapt.provers.escargot.Escargot
import gapt.provers.{ OneShotProver, Prover }
import gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import gapt.provers.sat.Sat4j
import gapt.provers.smtlib.Z3
import gapt.provers.verit.VeriT
import gapt.utils.{ Logger, Maybe }

trait GrammarFindingMethod {
  def findGrammars( lang: Set[Expr] ): Option[VTRATG]
  def name: String
}

case class MaxSATMethod( solver: MaxSATSolver, nonTerminalLengths: Int* ) extends GrammarFindingMethod {
  override def findGrammars( lang: Set[Expr] ): Option[VTRATG] =
    Some( findMinimalVTRATG( lang, nonTerminalLengths, solver ) )

  override def name: String = s"${nonTerminalLengths.mkString( "_" )}_maxsat"
}
object MaxSATMethod {
  def apply( nonTerminalLengths: Int* ): MaxSATMethod =
    MaxSATMethod( bestAvailableMaxSatSolver, nonTerminalLengths: _* )
}

case object ReforestMethod extends GrammarFindingMethod {
  def findGrammars( lang: Set[Expr] ) = {
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
  def apply( encoding: InstanceTermEncoding, g: VTRATG ): SchematicExtendedHerbrandSequent = {
    val us = encoding.endSequent zip encoding.symbols map {
      case ( u, sym ) =>
        u.asInstanceOf[FOLFormula] -> g.rightHandSides( g.startSymbolNT ).map( _.head ).toList.
          collect { case Apps( `sym`, args ) => args map { _.asInstanceOf[FOLTerm] } }
    }
    val slist = g.nonTerminals.filter( _ != g.startSymbolNT ).
      map { a => a.map( _.asInstanceOf[FOLVar] ) -> g.rightHandSides( a ).toList.map( _.map( _.asInstanceOf[FOLTerm] ) ) }.
      filter( _._2.nonEmpty ).toList

    SchematicExtendedHerbrandSequent( us, slist )
  }
}

object sehsToVTRATG {
  def apply( encoding: InstanceTermEncoding, sehs: SchematicExtendedHerbrandSequent ): VTRATG = {
    val freeVars = freeVariables( sehs.us.elements.flatMap { _._2 } ++ sehs.ss.flatMap { _._2 } flatten ) ++ sehs.eigenVariables.flatten
    val startSymbol = rename( Var( "x", encoding.instanceTermType ), freeVars )
    val nonTerminals = sehs.eigenVariables.map( _.toList )
    val instances = for ( ( f, us ) <- sehs.us; u <- us ) yield instantiate( f, u )
    val productionsFromAx = for ( t <- encoding encode instances ) yield List( startSymbol ) -> List( t )
    val otherProds = for ( ( ev, ss ) <- sehs.ss; s <- ss ) yield ev -> s
    val productions = productionsFromAx ++ otherProds

    val grounding = FOLSubstitution( freeVariables( productions flatMap { _._2 } ) diff nonTerminals.flatten.toSet map {
      case FOLVar( n ) => FOLVar( n ) -> FOLConst( n )
    } )

    VTRATG( startSymbol, List( startSymbol ) +: nonTerminals, productions map { p => p._1.toList -> grounding( p._2 ).toList } )
  }
}

object CutIntroduction {
  val logger = Logger( "cutintro" )
  import logger._

  class CutIntroException( msg: String ) extends Exception( msg )
  class NonCoveringGrammarException( grammar: VTRATG, term: Expr )
    extends CutIntroException( s"Grammar does not cover the following term in the Herbrand set:\n$term\n\n$grammar" )
  /**
   * Thrown if Extended Herbrand Sequent is unprovable. In theory this does not happen.
   * In practice it does happen if the method used for searching a proof covers a too
   * weak theory (e.g. no equality) or is not complete.
   */
  class UnprovableException( msg: String, sequent: HOLSequent ) extends CutIntroException( s"$msg\n$sequent" )

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

        override def runSession[A]( program: Session[A] ) = smtSolver.runSession( program )
        override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = smtSolver isValid s
        override def getLKProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ) = EquationalLKProver getLKProof s
      }
    }
    case object PureFOL extends BackgroundTheory {
      val hasEquality = false
      object prover extends OneShotProver {
        override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ) = LKProver getLKProof seq
        override def isValid( seq: HOLSequent )( implicit ctx: Maybe[Context] ) = Sat4j isValid seq
      }
    }

    def guess( sequent: HOLSequent ): BackgroundTheory =
      if ( atoms( sequent ).exists( Eq.unapply( _ ).isDefined ) ) Equality else PureFOL
    def guess( lk: LKProof ): BackgroundTheory =
      if ( containsEqualityReasoning( lk ) ) Equality else PureFOL
    def guess( p: ResolutionProof ): BackgroundTheory =
      if ( containsEquationalReasoning( p ) ) Equality else PureFOL
  }

  abstract case class InputProof private (
      expansionProof:   ExpansionProof,
      backgroundTheory: BackgroundTheory ) {
    require(
      isPrenexSigma1( expansionProof.shallow ),
      "Cut-introduction requires first-order prenex end-sequents without strong quantifiers" )
  }
  object InputProof {
    def apply( expansionProof: ExpansionProof, backgroundTheory: BackgroundTheory ): InputProof =
      if ( isPrenex( expansionProof.shallow ) )
        new InputProof( expansionProof, backgroundTheory ) {}
      else
        new InputProof( prenexifyET( expansionProof ), backgroundTheory ) {}

    implicit def fromLK( p: LKProof ): InputProof =
      apply( eliminateCutsET( LKToExpansionProof( p ) ), BackgroundTheory.guess( p ) )

    implicit def fromExpansionProof( p: ExpansionProof ): InputProof =
      apply( p, BackgroundTheory.guess( p.shallow ) )

    implicit def fromResolutionProof( p: ResolutionProof ): InputProof =
      apply( ResolutionToExpansionProof( p ), BackgroundTheory.guess( p ) )
  }

  private def solStructMetrics( solStruct: SolutionStructure, name: String ) = {
    logger.metric( s"${name}sol_lcomp", solStruct.formulas.map( lcomp( _ ) ).sum )
    logger.metric( s"${name}sol_scomp", solStruct.formulas.map( expressionSize( _ ) ).sum )
    logger.metric( s"${name}sol_nclauses", solStruct.formulas.map( f => CNFp( f ).size ).sum )
    val clauseSizes = solStruct.formulas.flatMap( CNFp.apply ).map( _.size )
    logger.metric( s"${name}sol_maxclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.max )
    logger.metric( s"${name}sol_avgclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.sum.toFloat / clauseSizes.size )
  }

  def compressToSolutionStructure(
    inputProof:       InputProof,
    method:           GrammarFindingMethod = DeltaTableMethod(),
    useInterpolation: Boolean              = false ): Option[SolutionStructure] = {
    val InputProof( ep, backgroundTheory ) = inputProof

    if ( useInterpolation && !backgroundTheory.hasEquality )
      return compressToSolutionStructure( InputProof( ep, BackgroundTheory.Equality ), method, useInterpolation )

    logger.metric( "quant_input", numberOfInstancesET( ep.expansionSequent ) )

    info( s"Quantifier inferences in the input proof: ${numberOfInstancesET( ep.expansionSequent )}" )

    val endSequent = ep.shallow
    info( s"End sequent: $endSequent" )

/********** Term set Extraction **********/
    val encoding = InstanceTermEncoding( endSequent )
    val termset = groundTerms( encoding encode ep )
    val weightedTermsetSize = termset.view.map { case Apps( _, args ) => args.size }.sum

    logger.metric( "termset", termset.size )
    logger.metric( "termset_wsize", weightedTermsetSize )
    logger.metric( "termset_scomp", termset.toSeq map { expressionSize( _ ) } sum )
    logger.metric( "termset_trivial", termset.size == termset.map { case Apps( r, _ ) => r }.size )
    info( s"Size of term set: ${termset.size} (weighted by root symbol arity = $weightedTermsetSize)" )

    val herbrandSequent = extractInstances( ep )
    val herbrandSequentProof = backgroundTheory.prover.getLKProof( herbrandSequent ).getOrElse {
      throw new UnprovableException( "Cannot prove Herbrand sequent.", herbrandSequent )
    }
    logger.metric( "hs_lcomp", herbrandSequent.elements.map( lcomp( _ ) ).sum )
    logger.metric( "hs_scomp", expressionSize( herbrandSequent.toDisjunction ) )
    logger.metric( "hs_lkinf", herbrandSequentProof.treeLike.size )

/********** Grammar finding **********/
    logger.time( "grammar" ) {
      method.findGrammars( termset )
    }.filter { g =>
      g.productions.exists( _._1 != g.startSymbolNT )
    }.orElse {
      info( "No grammar found." )
      None
    }.flatMap { vtratGrammar =>
      val generatedLanguage = vtratGrammar.language
      logger.metric( "grammar_lang_size", generatedLanguage.size )
      termset foreach { term =>
        if ( !( generatedLanguage contains term ) )
          throw new NonCoveringGrammarException( vtratGrammar, term )
      }

      logger.metric( "grammar_size", vtratGrammar.size )
      logger.metric( "grammar_wsize", vtratGrammar.weightedSize )
      logger.metric( "grammar_scomp", vtratGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )

      info( s"Smallest grammar of size ${vtratGrammar.size} (weighted by vector size = ${vtratGrammar.weightedSize}):\n$vtratGrammar" )

      val grammar = vtratgToSEHS( encoding, vtratGrammar )

      val canonicalSS = SolutionStructure(
        grammar,
        if ( useInterpolation )
          solutionViaInterpolation( grammar )
        else
          computeCanonicalSolution( grammar ) )
      require( canonicalSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( canonicalSS, "can" )

      val minimizedSS = logger.time( "minsol" ) { improveSolutionLK( canonicalSS, backgroundTheory.prover, backgroundTheory.hasEquality ) }
      for ( ( cf, i ) <- minimizedSS.formulas.zipWithIndex )
        info( s"CNF of minimized cut-formula number $i:\n${CNFp( cf ).map( "  " + _ ).mkString( "\n" )}" )
      require( minimizedSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( minimizedSS, "min" )

      val beautifiedSS = logger.time( "beausol" ) { beautifySolution( minimizedSS ) }
      require( beautifiedSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( beautifiedSS, "beau" )

      val lcompCanonicalSol = canonicalSS.formulas.map( lcomp( _ ) ).sum
      val lcompMinSol = minimizedSS.formulas.map( lcomp( _ ) ).sum
      val lcompBeauSol = beautifiedSS.formulas.map( lcomp( _ ) ).sum
      val beauGrammar = sehsToVTRATG( encoding, beautifiedSS.sehs )
      logger.metric( "beaugrammar_size", beauGrammar.size )
      logger.metric( "beaugrammar_wsize", beauGrammar.weightedSize )
      logger.metric( "beaugrammar_scomp", beauGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )
      logger.metric( "beausol", beautifiedSS.formulas.map( _.toString ) )

      if ( beautifiedSS.formulas.nonEmpty ) {
        if ( beautifiedSS.sehs == minimizedSS.sehs ) {
          info( "Beautification did not change the grammar." )
        } else {
          info( s"Beautified grammar of size ${beauGrammar.size} (weighted by vector size = ${beauGrammar.weightedSize}):\n$beauGrammar" )
        }
        if ( beautifiedSS == minimizedSS ) {
          info( "Beautification did not change the solution." )
        } else {
          info( s"Size of the beautified solution: $lcompBeauSol" )
          for ( ( cf, i ) <- beautifiedSS.formulas.zipWithIndex )
            info( s"CNF of minimized cut-formula number $i:\n${CNFp( cf ).map( "  " + _ ).mkString( "\n" )}" )
        }
        info( s"Size of the canonical solution: $lcompCanonicalSol" )
        info( s"Size of the minimized solution: $lcompMinSol" )

        val ehsSequent = beautifiedSS.getDeep
        val ehsResolutionProof = backgroundTheory.prover.getLKProof( ehsSequent ).getOrElse {
          throw new UnprovableException( "Cannot prove extended Herbrand sequent.", ehsSequent )
        }
        logger.metric( "ehs_lcomp", ehsSequent.elements.map( lcomp( _ ) ).sum )
        logger.metric( "ehs_scomp", expressionSize( ehsSequent.toDisjunction ) )
        logger.metric( "ehs_lkinf", ehsResolutionProof.treeLike.size )

        Some( beautifiedSS )
      } else {
        info( "No non-trivial lemma found." )
        None
      }
    }
  }

  def constructLKProof( solStruct: SolutionStructure, backgroundTheory: BackgroundTheory ): LKProof = {
    val proofWithStructuralRules = logger.time( "prcons" ) {
      buildProofWithCut( solStruct, backgroundTheory.prover )
    }

    val proof = logger.time( "cleanproof" ) {
      cleanStructuralRules( proofWithStructuralRules )
    }

    logger.metric( "lkcuts_output", cutsNumber( proof ) )
    logger.metric( "lkinf_output", rulesNumber( proof ) )
    logger.metric( "lkquant_output", quantRulesNumber( proof ) )
    info( s"Number of cuts introduced: ${cutsNumber( proof )}" )
    info( s"Total inferences in the proof with cut(s): ${rulesNumber( proof )}" )
    info( s"Quantifier inferences in the proof with cut(s): ${quantRulesNumber( proof )}" )

    proof
  }

  def apply(
    inputProof:       InputProof,
    method:           GrammarFindingMethod = DeltaTableMethod(),
    useInterpolation: Boolean              = false ): Option[LKProof] =
    if ( useInterpolation && !inputProof.backgroundTheory.hasEquality )
      apply(
        InputProof( inputProof.expansionProof, BackgroundTheory.Equality ),
        method, useInterpolation )
    else
      compressToSolutionStructure( inputProof, method, useInterpolation ).
        map( constructLKProof( _, inputProof.backgroundTheory ) )

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
    import gapt.proofs.gaptic._

    var state = ProofState(
      for ( ( formula, idx ) <- solStruct.endSequent.zipWithIndex )
        yield idx.toString -> formula )

    def addNewInstances( instances: FOLSequent ) =
      currentGoal.flatMap( curGoal => haveInstances( instances.distinct diff curGoal.conclusion ) )

    def insertProofOfSolutionCondition( i: Int ) = {
      val solCond = solStruct.instantiatedSolutionCondition( i )
      insert( prover.getLKProof( solCond ).
        getOrElse( throw new UnprovableException( s"Cannot prove solution condition ${i + 1}", solCond ) ) )
    }

    for ( ( ( evs, ss ), i ) <- solStruct.sehs.ss.zipWithIndex.reverse ) {
      state += addNewInstances( solStruct.sehs.esInstancesInScope( i + 1 ) )

      state += cut( s"cut$i", solStruct.cutFormulas( i ) )
      for ( ev <- evs ) state += allR( s"cut$i", ev )

      state += focus( 1 )
      for ( inst <- ss ) state += allL( s"cut$i", inst: _* )
      state += insertProofOfSolutionCondition( i )
    }

    state += addNewInstances( solStruct.sehs.endSequentInstances )
    state += insertProofOfSolutionCondition( -1 )

    state.result
  }
}

