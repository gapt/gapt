package at.logic.gapt.provers.escargot.impl

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.models.PropositionalModel
import at.logic.gapt.proofs.{ HOLClause, HOLSequent, MutableContext, Sequent }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.escargot.{ LPO, TermOrdering }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.utils.logger._

import scala.collection.mutable

class Cls( val state: EscargotState, val proof: ResolutionProof, val index: Int ) {
  def clause = proof.conclusion
  def assertion = proof.assertions

  def clauseWithAssertions = ( clause, assertion )

  val maximal = for {
    ( a, i ) <- clause.zipWithIndex.elements
    if !clause.elements.exists { x => a != x && state.termOrdering.lt( a, x ) }
  } yield i

  val selected = ( maximal.filter { _.isAnt } ++ clause.indicesSequent.antecedent ).take( 1 )

  val weight = clause.elements.map { expressionSize( _ ) }.sum

  override def toString = s"[$index] ${proof.stringifiedConclusion( state.ctx )}   (max = ${maximal mkString ", "}) (sel = ${selected mkString ", "}) (w = $weight)"
  override def hashCode = index
}

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

  var newlyDerived = Set[Cls]()
  val usable = mutable.Set[Cls]()
  var workedOff = Set[Cls]()
  val locked = mutable.Set[( Cls, Option[HOLClause] )]()

  // This formula should always be unsatisfiable.
  def stateAsFormula: Formula = And {
    ( newlyDerived.view ++ usable ++ workedOff ++ locked.map( _._1 ) ++ emptyClauses.values ).map { c =>
      c.proof.assertions.toNegConjunction --> universalClosure( c.proof.conclusion.toFormula )
    }
  } | And { ( newlyDerived.view ++ usable ++ workedOff ).map { c => universalClosure( c.proof.conclusion.toFormula ) } }

  var avatarModel = PropositionalModel( Map() )
  var emptyClauses = mutable.Map[HOLClause, Cls]()
  def isActive( cls: Cls ): Boolean = isActive( cls.assertion )
  def isActive( assertion: HOLClause ): Boolean =
    avatarModel( assertion.toNegConjunction )

  def preprocessing() =
    for ( r <- preprocessingRules )
      newlyDerived = r.preprocess( newlyDerived, workedOff )

  def trySetAssertion( assertion: HOLClause, value: Boolean ) =
    for ( ( atom, i ) <- assertion.zipWithIndex )
      trySetAvatarAtom( atom, if ( value ) i.isSuc else i.isAnt )
  def trySetAvatarAtom( atom: Atom, value: Boolean ) =
    if ( !avatarModel.assignment.isDefinedAt( atom ) )
      avatarModel = PropositionalModel( avatarModel.assignment + ( atom -> value ) )

  def clauseProcessing() = {
    // extend avatar model
    for ( c <- newlyDerived )
      trySetAssertion( c.assertion, c.clause.nonEmpty )

    for ( c <- newlyDerived ) {
      if ( c.clause.isEmpty ) {
        emptyClauses( c.assertion ) = c
        if ( !avatarModel( c.assertion.toDisjunction ) )
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

  def inferenceComputation( given: Cls ): Boolean = {
    val inferred = mutable.Set[Cls]()
    var discarded = false

    for ( r <- inferences if !discarded ) {
      val ( i, d ) = r( given, workedOff )
      inferred ++= i
      for ( ( c, reason ) <- d ) {
        workedOff -= c
        if ( c == given ) discarded = true
        if ( !reason.isSubMultisetOf( c.assertion ) )
          locked += ( c -> Some( reason ) )
      }
    }

    if ( !discarded ) workedOff += given
    newlyDerived ++= inferred

    discarded
  }

  var strategy = 0
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

  def switchToNewModel( model: PropositionalModel ) = {
    avatarModel = PropositionalModel(
      for ( ( a, p ) <- avatarModel.assignment )
        yield a -> model.assignment.getOrElse( a, p ) )

    for ( ( cls, reason ) <- locked.toSet if isActive( cls ) && reason.forall { !isActive( _ ) } ) {
      locked -= ( cls -> reason )
      usable += cls
    }
    for ( cls <- usable.toSeq if cls.clause.isEmpty ) usable -= cls
    for ( cls <- workedOff.toSeq if !isActive( cls ) ) {
      workedOff -= cls
      locked += ( cls -> None )
    }
    for ( cls <- usable.toSeq if !isActive( cls ) ) {
      usable -= cls
      locked += ( cls -> None )
    }
  }

  def loop(): Option[ResolutionProof] = {
    preprocessing()
    clauseProcessing()

    while ( true ) {
      if ( usable exists { _.clause.isEmpty } ) {
        for ( cls <- usable if cls.clause.isEmpty && cls.assertion.isEmpty )
          return Some( cls.proof )
        Sat4j.solve( emptyClauses.keys ) match {
          case Some( newModel ) =>
            debug( s"sat splitting model: ${avatarModel.trueAtoms.toSeq.sortBy( _.toString ).mkString( ", " )}".replace( '\n', ' ' ) )
            switchToNewModel( newModel )
          case None =>
            return Some( emptyClauses.get( Sequent() ).map( _.proof ).getOrElse {
              Sat4j.getResolutionProof( emptyClauses.values.map( cls => AvatarContradiction( cls.proof ) ) ).get
            } )
        }
      }
      if ( usable.isEmpty )
        return None

      val given = choose()
      usable -= given

      val discarded = inferenceComputation( given )

      debug( s"[wo=${workedOff.size},us=${usable.size}] ${if ( discarded ) "discarded" else "kept"}: $given".replace( '\n', ' ' ) )

      preprocessing()
      clauseProcessing()
    }

    None
  }
}
