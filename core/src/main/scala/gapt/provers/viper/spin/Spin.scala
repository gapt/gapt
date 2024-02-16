package gapt.provers.viper.spin

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.ty.TArr
import gapt.expr.ty.Ty
import gapt.expr.util.ConditionalNormalizer
import gapt.expr.util.ConditionalReductionRule
import gapt.expr.util.LambdaPosition
import gapt.expr.util.LambdaPosition.Choice
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.formats.tip.TipProblem
import gapt.logic.hol.skolemize
import gapt.proofs.ContextSection
import gapt.proofs.HOLClause
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.simplificationRules
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.resolution.ResolutionToLKProof
import gapt.proofs.resolution.mapInputClauses
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.withSection
import gapt.provers.escargot.Escargot
import gapt.provers.escargot.impl.Cls
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.escargot.impl.EscargotLogger.info
import gapt.provers.escargot.impl.EscargotState
import gapt.provers.sat.Sat4j
import gapt.provers.viper.aip.axioms.Axiom
import gapt.provers.viper.aip.axioms.SequentialInductionAxioms
import gapt.provers.viper.aip.axioms.StandardInductionAxioms
import gapt.provers.viper.grammars.enumerateTerms
import gapt.utils.NameGenerator
import org.sat4j.specs.ContradictionException

import scala.collection.mutable

// TODO: sampleTestTerms should probably not be 5 but something dependent on the number of constructors
/**
 *
 * @param performGeneralization Apply generalization to derived clauses.
 * @param sampleTestTerms The number of test terms to use for testing.
 * @param acceptNotNormalized Accept formulas for which no counterexample could be found because the samples do not
 * reduce to literal form (e.g. if the formula contains non-simplifiable Skolem constants as in nil = s₁).
 * @param splitting
 * @param equality
 * @param propositional
 */
case class SpinOptions(
    performGeneralization: Boolean = true,
    sampleTestTerms:       Int     = 5,
    acceptNotNormalized:   Boolean = false,
    splitting:             Boolean = true,
    equality:              Boolean = true,
    propositional:         Boolean = false )

object Spin {
  def apply( opts: SpinOptions = SpinOptions() ): Spin =
    new Spin( opts )
}

class Spin( opts: SpinOptions ) {

  private val performGeneralization: Boolean = opts.performGeneralization

  /**
   * Proves the given sequent by using induction.
   *
   * @param sequent The sequent to be proven.
   * @param ctx Defines the constants, types, etc.
   * @return An inductive proof the sequent is provable with the prover's induction schemes, otherwise None or
   *         the method does not terminate.
   */
  def inductiveLKProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): Option[LKProof] = {
    val seq = labeledSequentToHOLSequent( sequent )

    withSection { section =>
      val ground = section.groundSequent( seq )

      // Perform an initial induction while the goal has not been split across several clauses
      val goals = ground.succedent
      val goalAxioms = goals flatMap ( goal => clauseAxioms( skolemize( goal ) +: Sequent() )( ctx ) )
      val goalGround = goalAxioms.map( _.formula ) ++: ground

      val cnf = structuralCNF( goalGround )( ctx )
      val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap

      val clauses = cnfMap.keySet.map( _.map( _.asInstanceOf[Atom] ) )

      val prf = getResolutionProofWithAxioms( clauses )

      prf map {
        case ( resolution, prfAxioms, indMap ) =>
          val axioms = goalAxioms ++ prfAxioms.toSeq
          val res = mapInputClauses( resolution )( cnfMap ++ indMap )
          val lk = ResolutionToLKProof( res )
          val wlk = WeakeningContractionMacroRule( lk, axioms.map( _.formula ) ++: ground )
          val cut = cutAxioms( wlk, axioms )
          cut
      }
    }
  }

  private def clauseAxioms( clause: HOLSequent )( implicit ctx: Context ): Seq[Axiom] =
    new AxiomGenerator( opts ).axioms( clause )

  private def getResolutionProofWithAxioms( cnf: Iterable[HOLClause] )( implicit ctx: MutableContext ): Option[( ResolutionProof, Set[Axiom], Map[HOLSequent, ResolutionProof] )] = {
    val hasEquality = opts.equality && cnf.flatMap( _.elements ).exists { case Eq( _, _ ) => true; case _ => false }
    val isPropositional = opts.propositional || cnf.flatMap { freeVariables( _ ) }.isEmpty

    val state = new SpinState( ctx )
    Escargot.setupDefaults( state, opts.splitting, hasEquality, isPropositional )
    state.nameGen = rename.awayFrom( ctx.constants.toSet ++ cnf.view.flatMap( constants.nonLogical( _ ) ) )
    state.termOrdering = Escargot.lpoHeuristic( cnf, ctx.constants )
    state.newlyDerived ++= cnf.map {
      state.InputCls
    }
    state.loopWithAxioms()
  }

  /**
   * Cuts the specified axioms from the proof.
   *
   * @param proof The proof from which some axioms are to be cut. The end-sequent of this proof must
   *              contain the given axioms.
   * @param axioms The axioms to be cut out of the proof.
   * @return A proof whose end-sequent does not contain the specified axioms.
   */
  private def cutAxioms( proof: LKProof, axioms: Seq[Axiom] ): LKProof =
    axioms.foldRight( proof ) { ( axiom, mainProof ) =>
      if ( mainProof.conclusion.antecedent contains axiom.formula )
        CutRule( axiom.proof, mainProof, axiom.formula )
      else
        mainProof
    }

  private class SpinState( override val ctx: MutableContext ) extends EscargotState( ctx ) {

    private var inductedClauses = Set.empty[HOLSequent]
    private var addedAxioms = Set.empty[Axiom]
    private val possibleAxioms = mutable.Queue.empty[Axiom]
    private var cnfMap = Map.empty[HOLSequent, ResolutionProof]
    private var loopCount = 0
    private var inductCutoff = 16
    private val section = new ContextSection( ctx )

    def loopWithAxioms(): Option[( ResolutionProof, Set[Axiom], Map[HOLSequent, ResolutionProof] )] =
      loop().map { ( _, addedAxioms, cnfMap ) }

    override def loop(): Option[ResolutionProof] = {
      try {
        preprocessing()
        clauseProcessing()

        while ( true ) {

          handleEmptyClauses() match {
            case Some( p ) => return Some( p )
            case _         =>
          }

          inferClausesByInduction()

          if ( usable.isEmpty )
            return None

          val `given` = choose()
          usable -= `given`

          generatePotentialInductionAxioms( `given` )

          val discarded = inferenceComputation( `given` )

          info( s"[wo=${workedOff.size},us=${usable.size}] ${if ( discarded ) "discarded" else "kept"}: ${`given`}".replace( '\n', ' ' ) )

          preprocessing()
          clauseProcessing()

          loopCount += 1
        }
        None
      } catch {
        case _: ContradictionException =>
          Some( mkSatProof() )
      } finally {
        EscargotLogger.metric( "candidates", inductedClauses.size )
        EscargotLogger.metric( "added_axioms", addedAxioms.size )
      }
    }

    private def inferClausesByInduction(): Unit = {
      if ( allowInferClausesFromInductionAxioms() ) {
        loopCount = 0
        while ({ {
          if ( possibleAxioms.nonEmpty ) {
            inferClausesFromPotentialInductionAxioms()
            preprocessing()
            clauseProcessing()
            updateInductionCutoff()
          }
        } ;  usable.isEmpty }) ()
      }
    }

    private def inferClausesFromPotentialInductionAxioms(): Unit = {
      val newAxiom = selectPossibleInductionAxiom()
      val ( clauses, newMap ) = axiomClause( section, newAxiom )
      addedAxioms += newAxiom
      cnfMap ++= newMap
      newlyDerived ++= clauses
    }

    private def updateInductionCutoff(): Unit = {
      if ( addedAxioms.size % 5 == 0 )
        inductCutoff += 1
    }

    private def allowInferClausesFromInductionAxioms(): Boolean =
      usable.isEmpty || loopCount >= inductCutoff

    private def generatePotentialInductionAxioms( `given`: Cls ): Unit = {
      // TODO: this should probably be less restrictive now that we perform more subgoal generalization
      if ( performGeneralization || `given`.clause.exists( constants.nonLogical( _ ) exists ( isInductive( _ )( ctx ) ) ) &&
        !inductedClauses.contains( `given`.clause ) ) {
        EscargotLogger.time( "axiom_gen" ) {
          clauseAxioms( `given`.clause )( ctx ) foreach ( possibleAxioms.enqueue( _ ) )
        }
        inductedClauses += `given`.clause
      }
    }

    private def selectPossibleInductionAxiom(): Axiom = possibleAxioms.dequeue()
  }
}

class AxiomGenerator( options: SpinOptions ) {

  def axioms( cls: HOLSequent )( implicit ctx: Context ): Seq[Axiom] = {
    val f = negate( cls.toFormula )
    val occs = occurrences( f )( ctx )

    val underSame = occs.underSame.map( _.filter { t =>
      asInductiveConst( t )( ctx ).isDefined ||
        // Only generalise function-headed subterms with at least two primary occurences
        ( options.performGeneralization && funHeaded( t ) && occs.primary( t ).size >= 2 )
    } )

    underSame.toSeq.flatMap {
      case ts if ts.isEmpty => Seq()
      case ts if ts.size == 1 =>
        // This term only appears alone in primary position, so we do a regular induction on it.
        val t = ts.head
        // Passing in the same occurrences is okay, as we only change proper subterms
        val ( v, targets ) = getTargets( t, f, occs )

        // If we accept non-normalized terms, we may accept a too-general target and miss the actual one,
        // so use filter in that case to get all of them. This only occurs when lambdas are in play.
        def findOrFilter( f: Formula => Boolean ): Seq[Formula] =
          if ( options.acceptNotNormalized ) targets.filter( f ) else targets.find( f ).toSeq

        findOrFilter( testFormula( _, List( v ) ) ) flatMap { targ =>
          val target = universalClosureExcept( quantifyAccumulators( targ, occs ), Set( v ) )
          StandardInductionAxioms( v, target )( ctx ).toOption.map( Seq( _ ) )
        }
      case ts =>
        // These terms appear together so we need to induct on all of them together for the definitions to reduce.
        // For each of them, we might need to generalize passive occurrences, so we calculate a sequence of less and
        // less general formulas to be tested.

        def buildTargets( ts: Set[Expr] ): Seq[( Seq[Var], Formula )] = {
          ts.foldLeft( Seq( ( Seq.empty[Var], f ) ) ) {
            case ( vsfs, t ) =>
              vsfs.flatMap {
                case ( vs, g ) =>
                  val ( v, ts ) = getTargets( t, g, occs )
                  ts map ( ( v +: vs, _ ) )
              }
          }
        }

        // Also generate targets where we don't generalise subterms, in case all of those fail tests.
        val targets = buildTargets( ts ) ++ buildTargets( ts.flatMap( asInductiveConst( _ )( ctx ) ) )

        targets.find { case ( vs, target ) => testFormula( target, vs.toList ) } flatMap {
          case ( vs, targ ) =>
            val target = universalClosureExcept( quantifyAccumulators( targ, occs ), vs.toSet )
            SequentialInductionAxioms()( Sequent() :+ ( "axiom", target ) )( ctx ).toOption
        }
    } flatten
  }

  private def universalClosureExcept( f: Formula, vars: Set[Var] ): Formula =
    All.Block( ( freeVariables( f ) -- vars ).toSeq, f )

  private def occurrences( f: Formula )( implicit ctx: Context ): Occurences =
    new OccurrencesFinder()( ctx ).apply( f )

  private def testFormula( f: Formula, xs: List[Var] )( implicit ctx: Context ): Boolean =
    new FormulaTester( options.acceptNotNormalized, options.sampleTestTerms )( ctx ).apply( f, xs )

  private def funHeaded( e: Expr )( implicit ctx: Context ): Boolean =
    e match {
      case Apps( c: Const, _ ) =>
        ctx.conditionalReductionRules.exists( _.lhsHead == c ) && !lambdaType( c.ty.toString )
      case _ => false
    }

  // Given a term c to induct over in f, returns a fresh induction variable
  // and a prioritized list of induction goals, the first more general than the next.
  private def getTargets( c: Expr, f: Formula, occs: Occurences ): ( Var, Seq[Formula] ) = {
    val primPoses = occs.primary.getOrElse( c, Seq() )
    val passPoses = occs.passive.getOrElse( c, Seq() )
    val nameGen: NameGenerator = new NameGenerator( freeVariables( f ).map( _.name ) )
    val v = Var( nameGen.fresh( "ind" ), c.ty )

    var targets = List( replaceExpr( f, c, v ) )

    if ( options.performGeneralization && primPoses.size >= 2 && passPoses.nonEmpty ) {
      // Induct only on primary occurences, i.e. generalize
      targets ::= primPoses.foldLeft( f )( ( g, pos ) => g.replace( HOLPosition.toHOLPosition( g )( pos ), v ) )
    }

    ( v, targets )
  }

  private def quantifyAccumulators( f: Formula, occs: Occurences )( implicit ctx: Context ): Formula = {
    val accsPoses = occs.accumulators.view.filterKeys( asInductiveConst( _ )( ctx ).isDefined ).toMap

    accsPoses.foldLeft( f ) {
      case ( g, ( acc, _ ) ) =>
        val nameGen: NameGenerator = new NameGenerator( freeVariables( g ).map( _.name ) )
        val w = Var( nameGen.fresh( "ind" ), acc.ty )
        All( w, replaceExpr( g, acc, w ) )
    }
  }
}

// primary: A map from subexpressions that occur in primary positions to those positions.
// accumulators: A map from subexpressions that occur in accumulator positions to those positions.
// passive: A map from subexpressions that occur in passive positions to those positions.
// underSame: A set of subexpressions that occur in primary positions together directly under the same symbol.
//  The sets are transitive, so if a and b occur together and b and c occur together, underSame should contain a set
//  containing all of a, b and c.
case class Occurences(
    primary:      Map[Expr, Seq[LambdaPosition]],
    accumulators: Map[Expr, Seq[LambdaPosition]],
    passive:      Map[Expr, Seq[LambdaPosition]],
    underSame:    Set[Set[Expr]] )

class OccurrencesFinder()( implicit ctx: Context ) {

  def newPos( i: Int, size: Int, pos: List[Choice] ): List[Choice] =
    LambdaPosition.Right :: List.fill( size - i - 1 )( LambdaPosition.Left ) ++ pos

  // Split on the refl rules as well to treat = as having two primary positions
  private val allPositions: Map[Const, Positions] =
    Positions.splitRules( ctx.conditionalReductionRules.toSet ++ reflRules.conditionalRefl( ctx ) )

  var underSame = Set.empty[Set[Expr]]

  type Occs = ( Expr, List[Choice] )
  type Groups = ( Seq[Occs], Seq[Occs], Seq[Occs] ) // Primary, accumulator, passive

  def go( expr: Expr, pos: List[Choice], inPrimary: Boolean )( implicit ctx: Context ): Groups =
    expr match {
      case Apps( c: Const, rhsArgs ) if !allPositions.isDefinedAt( c ) =>
        rhsArgs.zipWithIndex.foldLeft[Groups]( ( Seq(), Seq(), Seq() ) ) {
          case ( ( prim, accs, pass ), ( e, i ) ) =>
            val p = newPos( i, rhsArgs.size, pos )
            val ( l, m, r ) = go( e, newPos( i, rhsArgs.size, pos ), inPrimary )
            ( l ++ prim, m ++ accs, r ++ pass )
        }
      case Apps( c: Const, rhsArgs ) =>
        // Treat uninterpreted functions as primary in all arguments
        val ( primaryArgs: Set[Int], accumulatorArgs: Set[Int], passiveArgs: Set[Int] ) =
          allPositions.get( c )
            .map( pos => ( pos.primaryArgs, pos.accumulatorArgs, pos.passiveArgs ) )
            .getOrElse( rhsArgs.zipWithIndex.map( _._2 ).toSet, Set(), Set() )

        // Anything occurring as a passive argument becomes passive, even subterms that appear in primary position.
        val pass1 = passiveArgs.toSeq flatMap { i =>
          val p = newPos( i, rhsArgs.size, pos )
          val ( l, m, r ) = go( rhsArgs( i ), p, inPrimary = false )
          ( rhsArgs( i ), p ) +: ( l ++ m ++ r )
        }

        // Treat passive and accumulator subterms of accumulator arguments as accumulators.
        val accs1 = accumulatorArgs.toSeq flatMap { i =>
          val p = newPos( i, rhsArgs.size, pos )
          val ( l, m, _ ) = go( rhsArgs( i ), p, inPrimary = false )
          ( rhsArgs( i ), p ) +: ( l ++ m )
        }

        // Gather subterms that occur together in primary position under the same defined symbol
        if ( inPrimary && !isConstructor( c )( ctx ) ) {
          val directSame = primaryArgs map rhsArgs

          // Consider all of e1, e2 and e3 under the same symbol in f(e1, f(e2, e3))
          // when f is primary in both positions.
          def collectNestedSame( exprs: Set[Expr] ): Set[Expr] = {
            exprs.flatMap {
              case Apps( d: Const, nestedArgs ) if c == d =>
                val here = primaryArgs map nestedArgs
                val there = collectNestedSame( here )
                here ++ there
              case _ => List()
            }
          }

          val same = directSame ++ collectNestedSame( directSame )

          // If any of the ones we just found appear in another cluster, we should merge that cluster and this one
          underSame.filter( _.intersect( same ).nonEmpty ) match {
            case Seq() => underSame += same
            case existings =>
              existings foreach {
                underSame -= _
              }
              // The current expr may be in one of the clusters, so remove it as it is replaced by subterms
              underSame += existings.foldLeft( same ) { case ( acc, set ) => acc union set } - expr
          }
        }

        // Primary occurences. Anything non-primary below keeps its status.
        val ( prim1, accs2, pass2 ) =
          primaryArgs.toSeq.foldLeft[Groups]( Seq(), Seq(), Seq() ) {
            case ( ( prim, accs, pass ), i ) =>
              val p = newPos( i, rhsArgs.size, pos )
              val ( l, m, r ) = go( rhsArgs( i ), p, inPrimary )
              ( ( rhsArgs( i ), p ) +: ( l ++ prim ), m ++ accs, r ++ pass )
          }
        ( prim1, accs1 ++ accs2, pass1 ++ pass2 )
      case App( a, b ) =>
        val ( l1, m1, r1 ) = go( a, LambdaPosition.Left :: pos, inPrimary )
        val ( l2, m2, r2 ) = go( b, LambdaPosition.Right :: pos, inPrimary )
        ( l1 ++ l2, m1 ++ m2, r1 ++ r2 )
      case _ => ( Seq(), Seq(), Seq() )
    }

  def apply( formula: Formula ): Occurences = {
    underSame = Set.empty
    val ( prim, accs, pass ) = go( formula, List(), inPrimary = true )

    val primMap = prim.groupBy( _._1 ).view.mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse: _* ) } ) toMap
    val accsMap = accs.groupBy( _._1 ).view.mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse: _* ) } ) toMap
    val passMap = pass.groupBy( _._1 ).view.mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse: _* ) } ) toMap

    Occurences( primMap, accsMap, passMap, underSame )
  }
}

object constructorRules {

  // Reduction rules for reducing equalities between equal constructors to equalities on their arguments
  // and equalities between distinct constructors to bottom.
  def apply( ctx: Context ): Set[ReductionRule] = {
    def makeArgs( ty: Ty ): List[Var] = {
      val nameGen: NameGenerator = ctx.newNameGenerator
      ty match {
        case TArr( s, t ) => Var( nameGen.fresh( "arg" ), s ) :: makeArgs( t )
        case _            => List()
      }
    }

    val baseTypes = ctx.get[BaseTypes].baseTypes.values
    val constructors = baseTypes.flatMap( ty => ctx.getConstructors( ty ).getOrElse( List() ) ).toSet

    val same = constructors.map { constr =>
      val lhsArgs = makeArgs( constr.ty )
      val rhsArgs = makeArgs( constr.ty )

      val res = And( lhsArgs.zip( rhsArgs ) map { case ( l, r ) => Eq( l, r ) } )

      ReductionRule( Eq( Apps( constr, lhsArgs ), Apps( constr, rhsArgs ) ), res )
    }

    val diff = for {
      c1 <- constructors
      c2 <- constructors
      if c1 != c2
      if resType( c1.ty ) == resType( c2.ty )
      lhsArgs = makeArgs( c1.ty )
      rhsArgs = makeArgs( c2.ty )
    } yield {
      ReductionRule( Eq( Apps( c1, lhsArgs ), Apps( c2, rhsArgs ) ), Bottom() )
    }

    same ++ diff
  }
}

object reflRules {
  // Equality is reflexive for all base types
  def apply( ctx: Context ): Set[ReductionRule] = {
    val baseTypes = ctx.get[BaseTypes].baseTypes.values.toSet
    baseTypes.map { ty =>
      val x = Var( "x", ty )
      ReductionRule( Eq( x, x ), Top() )
    }
  }
  def conditionalRefl( ctx: Context ): Set[ConditionalReductionRule] =
    reflRules( ctx ).map( ConditionalReductionRule( _ ) )
}

object isInductive {
  // Is c an inductive skolem constant, i.e. not a constructor
  def apply( c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( c.ty ) match {
      case None => false
      case Some( constrs ) =>
        !constrs.contains( c ) && !ctx.conditionalReductionRules.exists( rule => rule.lhsHead == c )
    }
}

object asInductiveConst {
  def apply( e: Expr )( implicit ctx: Context ): Option[Const] =
    e match {
      case c: Const if isInductive( c ) => Some( c )
      case _                            => None
    }
}

/**
 * Tests formulas for counter examples.
 *
 * The formulas are tested as follows: first the free variables and the quantifiers are instantiated by a some random
 * closed terms, the resulting formula is simplified according to the context, and tested for validity.
 */
class FormulaTester( acceptNotNormalized: Boolean, numberTestTerms: Int )( implicit ctx: Context ) {

  private val normalizer: ConditionalNormalizer =
    ConditionalNormalizer(
      ctx.conditionalReductionRules.toSet ++ reflRules.conditionalRefl( ctx ) ++ simplificationRules.conditionalRules ++
        constructorRules( ctx ).map( ConditionalReductionRule( _ ) ) )
  private var normalized = mutable.Map.empty[Formula, Formula]
  private val origConstants: Set[Const] = Context().constants.toSet
  private val sat = new Sat4j()

  /**
   * Checks a formula for counterexamples.
   *
   * @param vars The variables to be instant
   * @return
   */
  def apply( f: Formula, vars: List[Var] ): Boolean = {
    if ( numberTestTerms == 0 )
      return true

    val samples = makeSampleFormulas( f, vars )

    samples.map( normalize ).forall { nf =>
      check( nf ).getOrElse( acceptNotNormalized )
    }
  }

  // Returns Some( true ) if nf holds, Some( false ) if nf does not hold
  // and we have a normalised counter-example and None otherwise
  private def check( nf: Formula )( implicit ctx: Context ): Option[Boolean] =
    nf match {
      case Top() => Some( true )
      case Bottom() => Some( false )
      case _ if isValid( nf.asInstanceOf[Formula] ) || unblock( nf ) => Some( true )
      case _ if isEvaluable( nf ) => Some( false )
      case _ => None
    }

  // Replaces each occurrence of a VarOrConst from subs in e with opts.sampleTestTerms concrete values.
  // Returns a sequence of all permutations.
  private def makeSampleFormulas( f: Formula, subs: List[VarOrConst] ): LazyList[Formula] = {
    subs match {
      case List() => LazyList( f )
      case v :: vs =>
        val termStream = enumerateTerms.forType( v.ty )( ctx )
        val terms = termStream filter ( _.ty == v.ty ) take numberTestTerms
        terms.flatMap( t => makeSampleFormulas( f, vs ) map ( replaceExpr( _, v, t ) ) )
    }
  }

  // Some terms, like `sk_0 == sk_0` do not reduce even though any instantiation of the skolem terms reduces
  // to the same value. Attempt to unblock such terms by testing for all constructor forms of the terms involved.
  private def unblock( nf: Formula )( implicit ctx: Context ): Boolean = {
    val skolems = constants.nonLogical( nf ).flatMap( asInductiveConst( _ )( ctx ) )

    if ( skolems.isEmpty )
      return false

    // Try to unblock overly specific reduction rules by casing on skolems
    val alts = skolems.foldLeft( LazyList( nf ) ) {
      case ( ts, c ) =>
        val nConstrs = ctx.getConstructors( c.ty ).map( _.size ).getOrElse( 0 )
        val constrs = enumerateTerms.forType( c.ty ).filter( _.ty == c.ty ).take( nConstrs )
        ts.flatMap( t => constrs.map( s => replaceExpr( t, c, s ) ) )
    }

    alts.forall( alt => check( normalize( alt ) ).getOrElse( false ) )
  }

  private def normalize( f: Formula )( implicit ctx: Context ): Formula = {
    normalized.get( f ) match {
      case Some( nf ) => nf
      case None =>
        val nf = orientEqualities( normalizer.normalize( unfoldQuantifiers( f )( ctx ) ).asInstanceOf[Formula] )
        normalized += f -> nf
        nf
    }
  }

  private def isEvaluable( f: Formula )( implicit ctx: Context ): Boolean =
    constants.nonLogical( f ).forall( c => origConstants.contains( c ) || isConstructor( c )( ctx ) )

  private def isValid( f: Formula ): Boolean = sat.isValid( f )

  // Replace universals and existentials with a fixed number of tests of the formula
  private def unfoldQuantifiers( formula: Formula )( implicit ctx: Context ): Formula = {
    def samples( x: Var, f: Formula ): LazyList[Formula] = {
      val constrs = enumerateTerms.forType( x.ty ).filter( _.ty == x.ty ).take( numberTestTerms )
      constrs.map( replaceExpr( f, x, _ ) )
    }

    def go( f: Formula ): Formula =
      f match {
        case Ex( x, f )  => Or( samples( x, f ) map go )
        case All( x, f ) => And( samples( x, f ) map go )
        case Neg( a )    => Neg( go( a ) )
        case And( a, b ) => And( go( a ), go( b ) )
        case Or( a, b )  => Or( go( a ), go( b ) )
        case Imp( a, b ) => Imp( go( a ), go( b ) )
        case Iff( a, b ) => Iff( go( a ), go( b ) )
        case _           => f
      }

    go( formula )
  }

  // We need to orient equalities the same way around for the SAT solver to treat them the same
  private def orientEqualities( f: Formula ): Formula =
    f match {
      case Eq( lhs, rhs ) =>
        if ( lhs.toRawAsciiString <= rhs.toRawAsciiString )
          Eq( lhs, rhs )
        else
          Eq( rhs, lhs )

      case Neg( a )    => Neg( orientEqualities( a ) )
      case And( a, b ) => And( orientEqualities( a ), orientEqualities( b ) )
      case Or( a, b )  => Or( orientEqualities( a ), orientEqualities( b ) )
      case Imp( a, b ) => Imp( orientEqualities( a ), orientEqualities( b ) )
      case Iff( a, b ) => Iff( orientEqualities( a ), orientEqualities( b ) )
      case _           => f
    }
}

