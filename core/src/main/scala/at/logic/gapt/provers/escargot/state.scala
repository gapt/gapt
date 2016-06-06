package at.logic.gapt.provers.escargot.impl

import at.logic.gapt.expr._
import at.logic.gapt.models.{ Interpretation, MapBasedInterpretation }
import at.logic.gapt.proofs.{ HOLClause, Sequent }
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.provers.escargot.{ LPO, TermOrdering }
import at.logic.gapt.provers.sat.Sat4j
import at.logic.gapt.utils.NameGenerator
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

class Cls( val state: EscargotState, val proof: ResolutionProof, val index: Int ) {
  def clause = proof.conclusion.asInstanceOf[HOLClause]
  def assertion = proof.assertions.asInstanceOf[HOLClause]

  def clauseWithAssertions = ( clause, assertion )

  val maximal = for {
    ( a, i ) <- clause.zipWithIndex.elements
    if !clause.elements.exists { x => a != x && state.termOrdering.lt( a, x ) }
  } yield i

  val selected = ( maximal.filter { _.isAnt } ++ clause.indicesSequent.antecedent ).take( 1 )

  val weight = clause.elements.map { expressionSize( _ ) }.sum

  override def toString = s"[$index] $clause   (max = ${maximal mkString ", "}) (sel = ${selected mkString ", "}) (w = $weight) [$assertion]"
  override def hashCode = index
}

class EscargotState extends Logger {
  var termOrdering: TermOrdering = LPO()
  var nameGen = new NameGenerator( Seq() )
  var preprocessingRules = Seq[PreprocessingRule]()
  var inferences = Seq[InferenceRule]()

  private var clsIdx = 0
  def InputCls( clause: HOLClause ): Cls = { clsIdx += 1; new Cls( this, Input( clause ), clsIdx ) }
  def SimpCls( parent: Cls, newProof: ResolutionProof ): Cls = new Cls( this, newProof, parent.index )
  def DerivedCls( parent: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( this, newProof, clsIdx ) }
  def DerivedCls( parent1: Cls, parent2: Cls, newProof: ResolutionProof ): Cls = { clsIdx += 1; new Cls( this, newProof, clsIdx ) }

  var newlyDerived = Set[Cls]()
  val usable = mutable.Set[Cls]()
  var workedOff = Set[Cls]()
  val locked = mutable.Set[Cls]()

  var avatarModel = MapBasedInterpretation( Map() )
  var emptyClauses = mutable.Map[HOLClause, Cls]()
  def isActive( cls: Cls ): Boolean = isActive( cls.assertion )
  def isActive( assertion: HOLClause ): Boolean =
    avatarModel.interpret( assertion.toNegConjunction )

  def preprocessing() =
    for ( r <- preprocessingRules )
      newlyDerived = r.preprocess( newlyDerived, workedOff )

  def trySetAssertion( assertion: HOLClause, value: Boolean ) =
    for ( ( atom, i ) <- assertion.zipWithIndex )
      trySetAvatarAtom( atom, if ( value ) i.isSuc else i.isAnt )
  def trySetAvatarAtom( atom: HOLAtom, value: Boolean ) =
    if ( !avatarModel.model.isDefinedAt( atom ) )
      avatarModel = MapBasedInterpretation( avatarModel.model + ( atom -> value ) )

  def clauseProcessing() = {
    // extend avatar model
    for ( c <- newlyDerived )
      trySetAssertion( c.assertion, c.clause.nonEmpty )

    for ( c <- newlyDerived ) {
      if ( c.clause.isEmpty ) {
        emptyClauses( c.assertion ) = c
        if ( !avatarModel.interpret( c.assertion.toDisjunction ) )
          usable += c // trigger model recomputation
      }
      if ( isActive( c ) ) {
        usable += c
      } else if ( c.clause.nonEmpty ) {
        locked += c
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
      workedOff --= d
      if ( d contains given ) discarded = true
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

  def switchToNewModel( model: Interpretation ) = {
    avatarModel = MapBasedInterpretation(
      avatarModel.model.keys.map( a => a -> model.interpretAtom( a ) ).toMap
    )

    for ( cls <- locked.toSet if isActive( cls ) ) {
      locked -= cls
      usable += cls
    }
    for ( cls <- usable if cls.clause.isEmpty ) usable -= cls
    for ( cls <- workedOff if !isActive( cls ) ) {
      workedOff -= cls
      locked += cls
    }
    for ( cls <- usable if !isActive( cls ) ) {
      usable -= cls
      locked += cls
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
            debug( s"sat splitting model: ${avatarModel.model.keys.filter( newModel.interpretAtom ).toSeq.sortBy( _.toString ).mkString( ", " )}".replace( '\n', ' ' ) )
            switchToNewModel( newModel )
          case None =>
            return Some( emptyClauses.get( Sequent() ).map( _.proof ).getOrElse {
              Sat4j.getRobinsonProof( emptyClauses.values.map( cls => AvatarAbsurd( cls.proof ) ) ).get
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
