package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars._
import at.logic.gapt.grammars.reforest.Reforest
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning }
import at.logic.gapt.provers.Session.Session
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.{ OneShotProver, Prover }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.utils.{ Logger, metrics }

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

object CutIntroduction extends Logger {

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

    def guess( sequent: HOLSequent ): BackgroundTheory =
      if ( atoms( sequent ).exists( Eq.unapply( _ ).isDefined ) ) Equality else PureFOL
    def guess( lk: LKProof ): BackgroundTheory =
      if ( containsEqualityReasoning( lk ) ) Equality else PureFOL
    def guess( p: ResolutionProof ): BackgroundTheory =
      if ( containsEquationalReasoning( p ) ) Equality else PureFOL
  }

  abstract case class InputProof private (
      expansionProof:   ExpansionProof,
      backgroundTheory: BackgroundTheory
  ) {
    require(
      isFOLPrenexSigma1( expansionProof.shallow ),
      "Cut-introduction requires first-order prenex end-sequents without strong quantifiers"
    )
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
    metrics.value( s"${name}sol_lcomp", solStruct.formulas.map( lcomp( _ ) ).sum )
    metrics.value( s"${name}sol_scomp", solStruct.formulas.map( expressionSize( _ ) ).sum )
    metrics.value( s"${name}sol_nclauses", solStruct.formulas.map( f => CNFp( f ).size ).sum )
    val clauseSizes = solStruct.formulas.flatMap( CNFp.apply ).map( _.size )
    metrics.value( s"${name}sol_maxclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.max )
    metrics.value( s"${name}sol_avgclssize", if ( clauseSizes.isEmpty ) 0 else clauseSizes.sum.toFloat / clauseSizes.size )
  }

  def compressToSolutionStructure(
    inputProof: InputProof,
    method:     GrammarFindingMethod = DeltaTableMethod()
  ): Option[SolutionStructure] = {
    val InputProof( ep, backgroundTheory ) = inputProof

    metrics.value( "quant_input", numberOfInstancesET( ep.expansionSequent ) )

    info( s"Quantifier inferences in the input proof: ${numberOfInstancesET( ep.expansionSequent )}" )

    val endSequent = ep.shallow
    info( s"End sequent: $endSequent" )

    /********** Term set Extraction **********/
    val encoding = InstanceTermEncoding( endSequent )
    val termset = groundTerms( encoding encode ep )
    val weightedTermsetSize = termset.view.map { case Apps( _, args ) => args.size }.sum

    metrics.value( "termset", termset.size )
    metrics.value( "termset_wsize", weightedTermsetSize )
    metrics.value( "termset_scomp", termset.toSeq map { expressionSize( _ ) } sum )
    metrics.value( "termset_trivial", termset.size == termset.map { case Apps( r, _ ) => r }.size )
    info( s"Size of term set: ${termset.size} (weighted by root symbol arity = $weightedTermsetSize)" )

    val herbrandSequent = extractInstances( ep )
    val herbrandSequentProof = backgroundTheory.prover.getLKProof( herbrandSequent ).getOrElse {
      throw new UnprovableException( "Cannot prove Herbrand sequent.", herbrandSequent )
    }
    metrics.value( "hs_lcomp", herbrandSequent.elements.map( lcomp( _ ) ).sum )
    metrics.value( "hs_scomp", expressionSize( herbrandSequent.toDisjunction ) )
    metrics.value( "hs_lkinf", herbrandSequentProof.treeLike.size )

    /********** Grammar finding **********/
    metrics.time( "grammar" ) {
      method.findGrammars( termset )
    }.filter { g =>
      g.productions.exists( _._1 != g.startSymbolNT )
    }.orElse {
      info( "No grammar found." )
      None
    }.flatMap { vtratGrammar =>
      val generatedLanguage = vtratGrammar.language
      metrics.value( "grammar_lang_size", generatedLanguage.size )
      termset foreach { term =>
        if ( !( generatedLanguage contains term ) )
          throw new NonCoveringGrammarException( vtratGrammar, term )
      }

      metrics.value( "grammar_size", vtratGrammar.size )
      metrics.value( "grammar_wsize", vtratGrammar.weightedSize )
      metrics.value( "grammar_scomp", vtratGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )

      info( s"Smallest grammar of size ${vtratGrammar.size} (weighted by vector size = ${vtratGrammar.weightedSize}):\n$vtratGrammar" )

      val grammar = vtratgToSEHS( encoding, vtratGrammar )

      val canonicalSS = SolutionStructure( grammar, computeCanonicalSolution( grammar ) )
      require( canonicalSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( canonicalSS, "can" )

      val minimizedSS = metrics.time( "minsol" ) { improveSolutionLK( canonicalSS, backgroundTheory.prover, backgroundTheory.hasEquality ) }
      for ( ( cf, i ) <- minimizedSS.formulas.zipWithIndex )
        info( s"CNF of minimized cut-formula number $i:\n${CNFp( cf ).map( "  " + _ ).mkString( "\n" )}" )
      require( minimizedSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( minimizedSS, "min" )

      val beautifiedSS = metrics.time( "beausol" ) { beautifySolution( minimizedSS ) }
      require( beautifiedSS.isValid( backgroundTheory.prover ) )
      solStructMetrics( beautifiedSS, "beau" )

      val lcompCanonicalSol = canonicalSS.formulas.map( lcomp( _ ) ).sum
      val lcompMinSol = minimizedSS.formulas.map( lcomp( _ ) ).sum
      val lcompBeauSol = beautifiedSS.formulas.map( lcomp( _ ) ).sum
      val beauGrammar = sehsToVTRATG( encoding, beautifiedSS.sehs )
      metrics.value( "beaugrammar_size", beauGrammar.size )
      metrics.value( "beaugrammar_wsize", beauGrammar.weightedSize )
      metrics.value( "beaugrammar_scomp", beauGrammar.productions.toSeq flatMap { _._2 } map { expressionSize( _ ) } sum )
      metrics.value( "beausol", beautifiedSS.formulas.map( _.toString ) )

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
        metrics.value( "ehs_lcomp", ehsSequent.elements.map( lcomp( _ ) ).sum )
        metrics.value( "ehs_scomp", expressionSize( ehsSequent.toDisjunction ) )
        metrics.value( "ehs_lkinf", ehsResolutionProof.treeLike.size )

        Some( beautifiedSS )
      } else {
        info( "No non-trivial lemma found." )
        None
      }
    }
  }

  def constructLKProof( solStruct: SolutionStructure, backgroundTheory: BackgroundTheory ): LKProof = {
    val proofWithStructuralRules = metrics.time( "prcons" ) {
      buildProofWithCut( solStruct, backgroundTheory.prover )
    }

    val proof = metrics.time( "cleanproof" ) {
      cleanStructuralRules( proofWithStructuralRules )
    }

    metrics.value( "lkcuts_output", cutsNumber( proof ) )
    metrics.value( "lkinf_output", rulesNumber( proof ) )
    metrics.value( "lkquant_output", quantRulesNumber( proof ) )
    info( s"Number of cuts introduced: ${cutsNumber( proof )}" )
    info( s"Total inferences in the proof with cut(s): ${rulesNumber( proof )}" )
    info( s"Quantifier inferences in the proof with cut(s): ${quantRulesNumber( proof )}" )

    proof
  }

  def apply( inputProof: InputProof, method: GrammarFindingMethod = DeltaTableMethod() ): Option[LKProof] =
    compressToSolutionStructure( inputProof, method ) map { constructLKProof( _, inputProof.backgroundTheory ) }

  @deprecated( "Use CutIntroduction(...) instead.", since = "2.3" )
  def compressToLK( inputProof: InputProof, method: GrammarFindingMethod = DeltaTableMethod(), verbose: Boolean = false ): Option[LKProof] =
    apply( inputProof, method )

  @deprecated( "Use CutIntroduction(...) instead.", since = "2.3" )
  def compressLKProof( inputProof: InputProof, method: GrammarFindingMethod = DeltaTableMethod(), verbose: Boolean = false ): Option[LKProof] =
    apply( inputProof, method )

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
    import at.logic.gapt.proofs.gaptic._

    var state = ProofState(
      for ( ( formula, idx ) <- solStruct.endSequent.zipWithIndex )
        yield idx.toString -> formula
    )

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

