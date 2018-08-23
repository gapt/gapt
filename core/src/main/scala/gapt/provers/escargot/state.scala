package gapt.provers.escargot.impl

import gapt.expr._
import gapt.expr.hol.universalClosure
import gapt.proofs.{ HOLClause, HOLSequent, Sequent }
import gapt.proofs.resolution._
import gapt.provers.escargot.{ LPO, TermOrdering }
import gapt.provers.sat.Sat4j
import gapt.utils.Logger
import org.sat4j.minisat.SolverFactory
import Sat4j._
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.rup.RupProof
import org.sat4j.specs.{ ContradictionException, IConstr, ISolverService }
import org.sat4j.tools.SearchListenerAdapter

object EscargotLogger extends Logger( "escargot" ); import EscargotLogger._

import scala.collection.mutable

/**
 * Data structure for clauses derived in Escargot.
 *
 * @param state  Prover state that "produced" this clause.
 * @param proof  Resolution proof ending in this clause.
 * @param index  Serial number issued by the [[EscargotState]].  The index is a deterministic
 *               hash code, and also indicates how old the clause is.
 */
class Cls( val state: EscargotState, val proof: ResolutionProof, val index: Int ) {
  val clause = proof.conclusion
  def assertion = proof.assertions

  val ass = state.intern( assertion )

  def clauseWithAssertions = ( clause, assertion )

  val maximal = for {
    ( a, i ) <- clause.zipWithIndex.elements
    if !clause.elements.exists { x => a != x && state.termOrdering.lt( a, x ) }
  } yield i

  val selected = ( maximal.filter { _.isAnt } ++ clause.indicesSequent.antecedent ).take( 1 )

  val weight = clause.elements.map { expressionSize( _ ) }.sum

  val freeVars = freeVariables( clause )

  val literalFeatureVecs = clause.map( TermFeatureVec( _ ) )
  val featureVec = ClauseFeatureVec( literalFeatureVecs )

  def posResCands: Vector[Formula] = maximal.filter( _.isSuc ).map( clause( _ ) )
  def negResCands: Vector[Formula] =
    ( if ( selected.nonEmpty ) selected else maximal ).
      filter( _.isAnt ).map( clause( _ ) )
  def unitRwrLhs: Seq[( Expr, Expr, Boolean, Cls )] =
    clause match {
      case Sequent( Seq(), Seq( Eq( t, s ) ) ) =>
        def choose[T]( ts: T* ): Seq[T] = ts
        for {
          ( t_, s_, ltr ) <- choose( ( t, s, true ), ( s, t, false ) )
          if !t_.isInstanceOf[Var]
          if !state.termOrdering.lt( t_, s_ )
        } yield ( t_, s_, ltr, this )
      case _ => Seq.empty
    }

  override def toString = s"[$index] ${proof.stringifiedConclusion( state.ctx )}   (max = ${maximal mkString ", "}) (sel = ${selected mkString ", "}) (w = $weight)"
  override def hashCode = index
}

case class IndexedClsSet(
    clauses:     Set[Cls],
    posResCands: DiscrTree[Cls],
    negResCands: DiscrTree[Cls],
    unitRwrLhs:  DiscrTree[( Expr, Expr, Boolean, Cls )],
    state:       EscargotState ) {
  def size: Int = clauses.size

  def +( c: Cls ): IndexedClsSet =
    IndexedClsSet(
      clauses = clauses + c,
      posResCands = posResCands.insert( c.posResCands, c ),
      negResCands = negResCands.insert( c.negResCands, c ),
      unitRwrLhs = c.unitRwrLhs.foldLeft( unitRwrLhs )( ( dt, e ) => dt.insert( e._1, e ) ),
      state = state )
  def ++( cs: Iterable[Cls] ): IndexedClsSet =
    cs.foldLeft( this )( _ + _ )
  def -( c: Cls ): IndexedClsSet =
    IndexedClsSet(
      clauses = clauses - c,
      posResCands = posResCands.remove( c ),
      negResCands = negResCands.remove( c ),
      unitRwrLhs = unitRwrLhs.filter( _._4 != c ),
      state = state )
}
object IndexedClsSet {
  def apply( state: EscargotState ): IndexedClsSet =
    IndexedClsSet(
      clauses = Set(),
      posResCands = DiscrTree(),
      negResCands = DiscrTree(),
      unitRwrLhs = DiscrTree(),
      state = state )
}

/**
 * Main class of the Escargot superposition prover.
 *
 * A practical introduction to superposition provers can be found in [1], Section 3.
 *
 * Essentially, we start with a set of clauses and apply inferences until we either:
 * 1. have derived the empty clause, or
 * 2. applied all possible inferences without producing new clauses
 *
 * The clauses are stored in various sets, the main two ones are:
 *  * workedOff: all inferences between clauses in this set have already been applied
 *  * usable: these clauses have not yet been used in inferences
 *
 * In every iteration of the prover (see the loop method), we
 * 1. pick a "given" clause from usable (using the choose method)
 * 2. perform all inferences between the given clause and all clauses in workedOff
 * 2a. add the given clause to workedOff (unless discarded by an inference)
 * 3. now newlyDerived contains the newly derived clauses, and we perform preprocessing on them
 * 3a. the preprocessed clauses get moved to usable
 *
 * (The names are non-standard and picked from different sources with no regard for consistency, sorry.)
 *
 * Inferences: an [[InferenceRule]] is an operation that looks at the given clause,
 * and the set of worked off clauses; it returns a set of new clauses, plus a set of clauses that should be discarded.
 *
 * For example, [[StandardInferences.BackwardSubsumption]] is an inference rule: it returns no new clauses,
 * but the subsumed clauses in usable are returned as discarded.
 *
 * Avatar splitting: Escargot employs the Avatar splitting regime [2].  Clauses are annotated with
 * propositional assertions, see [[gapt.proofs.resolution.ResolutionProof]] for the syntax.  We always have a propositional
 * model (avatarModel), and only consider clauses whose assertions are true in this model (called "active" here).
 * Clauses whose assertions are false in the model are stored in locked.  Whenever we derive an empty clause,
 * we call the SAT solver to obtain a model in which every empty clause has a false assertion.
 * If there is no such model, then we have found a proof!
 *
 * [1] Weidenbach, Combining Superposition, Sorts and Splitting. Handbook of Automated Reasoning II, 2001
 * [2] Voronkov, AVATAR: The Architecture for first-order theorem provers. CAV 2014
 */
class EscargotState( val ctx: MutableContext ) {
  var termOrdering: TermOrdering = LPO()
  var nameGen = ctx.newNameGenerator
  var preprocessingRules = Seq[PreprocessingRule]()
  var inferences = Seq[InferenceRule]()

  private var clsIdx = 0
  def InputCls( clause: HOLSequent ): Cls = InputCls( Input( clause ) )
  def InputCls( proof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( this, proof, clsIdx ) }
  def SimpCls( parent: Cls, newProof: ResolutionProof ): Cls = new Cls( this, newProof, parent.index )
  def DerivedCls( parent: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( this, newProof, clsIdx ) }
  def DerivedCls( parent1: Cls, parent2: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( this, newProof, clsIdx ) }

  /** Clauses that have been derived in the current iteration. */
  var newlyDerived = Set[Cls]()
  /** We have not yet used these clauses in inferences. */
  val usable = mutable.Set[Cls]()
  /** All inferences between these clauses have already been applied. */
  var workedOff = IndexedClsSet( this )
  /**
   * Locked clauses have assertions that are false in the current model,
   * or are subsumed by a clause whose assertion is true in the current model.
   *
   * The optional clause is the assertion of the subsuming clause.
   */
  val locked = mutable.Set[( Cls, Option[Set[Int]] )]()

  /** This formula should always be unsatisfiable. */
  def stateAsFormula: Formula = And {
    ( newlyDerived.view ++ usable ++ workedOff.clauses ++ locked.map( _._1 ) ++ emptyClauses.values ).map { c =>
      c.proof.assertions.toNegConjunction --> universalClosure( c.proof.conclusion.toFormula )
    }
  } | And { ( newlyDerived.view ++ usable ++ workedOff.clauses ).map { c => universalClosure( c.proof.conclusion.toFormula ) } }

  /** SAT solver instance */
  val solver = SolverFactory.newDefault()
  val drup = mutable.Buffer[RupProof.Line]()
  solver.setSearchListener( new SearchListenerAdapter[ISolverService] {
    override def learnUnit( p: Int ) = drup += RupProof.Rup( Set( p ) )
    override def learn( c: IConstr ) = drup += RupProof.Rup( c )
  } )

  /** Map from assertion atoms to SAT solver atoms */
  val atomToSatSolver = mutable.Map[Atom, Int]()
  val satSolverToAtom = mutable.Map[Int, Atom]()
  def intern( atom: Atom ): Int =
    atomToSatSolver.getOrElseUpdate( atom, {
      val i = solver.nextFreeVarId( true )
      satSolverToAtom( i ) = atom
      i
    } )
  def intern( assertions: HOLClause ): Set[Int] =
    assertions.map( intern, -intern( _ ) ).elements.toSet
  def deintern( i: Int ): Atom =
    satSolverToAtom( i )
  def deinternLiteral( i: Int ): Formula =
    if ( i < 0 ) -deintern( -i ) else deintern( i )

  /** Current propositional Avatar model. */
  var avatarModel = Set[Int]()
  /** Empty clauses that have already been derived.  All assertions in the empty clauses are false. */
  var emptyClauses = mutable.Map[Set[Int], Cls]()
  /** Is the assertion of cls true in the current model? */
  def isActive( cls: Cls ): Boolean = isActive( cls.ass )
  /** Is the assertion true in the current model? */
  def isActive( assertion: HOLClause ): Boolean =
    intern( assertion ).subsetOf( avatarModel )
  /** Is the assertion true in the current model? */
  def isActive( assertion: Set[Int] ): Boolean =
    assertion.subsetOf( avatarModel )

  /** Pre-processes the clauses in newlyDerived.  The result is again in newlyDerived. */
  def preprocessing() =
    for ( r <- preprocessingRules )
      newlyDerived = r.preprocess( newlyDerived, workedOff )

  def trySetAssertion( assertion: Set[Int], value: Boolean ) =
    for ( a <- assertion ) trySetAvatarAtom( if ( value ) a else -a )
  def trySetAvatarAtom( atom: Int ) =
    if ( !avatarModel( -atom ) ) avatarModel += atom

  /** Moves clauses from newlyDerived into usable and locked. */
  def clauseProcessing() = {
    // extend avatar model
    for ( c <- newlyDerived )
      trySetAssertion( c.ass, c.clause.nonEmpty )

    for ( c <- newlyDerived ) {
      if ( c.clause.isEmpty ) {
        emptyClauses( c.ass ) = c
        solver.addClause( c.ass.toSeq.map( -_ ) )
        if ( isActive( c.ass ) )
          usable += c // trigger model recomputation
      }
      if ( isActive( c ) ) {
        usable += c
      } else if ( c.clause.nonEmpty ) {
        locked += ( c -> None )
      }
    }
    newlyDerived = Set()
  }

  /** Performs inferences between given and workedOff, and adds given to workedOff. */
  def inferenceComputation( given: Cls ): Boolean = {
    val inferred = mutable.Set[Cls]()
    var discarded = false

    for ( r <- inferences if !discarded ) {
      val ( i, d ) = r( given, workedOff )
      inferred ++= i
      for ( ( c, reason ) <- d ) {
        workedOff -= c
        if ( c == given ) discarded = true
        if ( !reason.subsetOf( c.ass ) )
          locked += ( c -> Some( reason ) )
      }
    }

    if ( !discarded ) workedOff += given
    newlyDerived ++= inferred

    discarded
  }

  var strategy = 0
  /** Chooses the next clause from usable. */
  def choose(): Cls = {
    strategy = ( strategy + 1 ) % 6
    if ( strategy < 1 ) usable minBy { _.index }
    else if ( strategy < 3 ) {
      val pos = usable filter { _.clause.antecedent.isEmpty }
      if ( pos isEmpty ) choose()
      else pos minBy { cls => ( cls.weight, cls.index ) }
    } else if ( strategy < 5 ) {
      val nonPos = usable filter { _.clause.antecedent.nonEmpty }
      if ( nonPos isEmpty ) choose()
      else nonPos minBy { cls => ( cls.weight, cls.index ) }
    } else {
      usable minBy { cls => ( cls.weight, cls.index ) }
    }
  }

  def switchToNewModel() = {
    avatarModel = solver.model().toSet

    for ( ( cls, reason ) <- locked.toSet if isActive( cls ) && reason.forall { !isActive( _ ) } ) {
      locked -= ( cls -> reason )
      usable += cls
    }
    for ( cls <- usable.toSeq if cls.clause.isEmpty ) usable -= cls
    for ( cls <- workedOff.clauses if !isActive( cls ) ) {
      workedOff -= cls
      locked += ( cls -> None )
    }
    for ( cls <- usable.toSeq if !isActive( cls ) ) {
      usable -= cls
      locked += ( cls -> None )
    }
  }

  def mkSatProof(): ResolutionProof =
    RupProof( emptyClauses.keys.toSeq.map( cls => RupProof.Input( cls.map( -_ ) ) ) ++ drup :+ RupProof.Rup( Set() ) ).
      toRes.toResolution( satSolverToAtom, cls => {
        val p = emptyClauses( cls.map( -_ ) ).proof
        if ( p.assertions.isEmpty ) p else AvatarContradiction( p )
      } )

  /** Main inference loop. */
  def loop(): Option[ResolutionProof] = try {
    preprocessing()
    clauseProcessing()

    while ( true ) {
      if ( usable exists { _.clause.isEmpty } ) {
        for ( cls <- usable if cls.clause.isEmpty && cls.assertion.isEmpty )
          return Some( cls.proof )
        if ( solver.isSatisfiable ) {
          info( s"sat splitting model: ${
            solver.model().filter( _ >= 0 ).map( deintern ).
              sortBy( _.toString ).mkString( ", " )
          }".replace( '\n', ' ' ) )
          switchToNewModel()
        } else {
          return Some( mkSatProof() )
        }
      }
      if ( usable.isEmpty )
        return None

      val given = choose()
      usable -= given

      val discarded = inferenceComputation( given )

      info( s"[wo=${workedOff.size},us=${usable.size}] ${if ( discarded ) "discarded" else "kept"}: $given".replace( '\n', ' ' ) )

      preprocessing()
      clauseProcessing()
    }

    None
  } catch {
    case _: ContradictionException =>
      Some( mkSatProof() )
  }
}
