package at.logic.gapt.proofs.expansionTrees

import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.dssupport.ListSupport.listComplements
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable.{ ListBuffer, HashMap => mMap }

/**
 * Given an expansion sequent S, this algorithm computes the list of expansion
 * sequents below S that are valid and minimal.
 */
object minimalExpansionSequents {
  /**
   * Applies the algorithm to a MultiExpansionSequent.
   * @param sequent The MultiExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: MultiExpansionSequent, prover: Prover ): Seq[MultiExpansionSequent] =
    new Minimizer( sequent, prover ).computeAllMinimal()

  /**
   * Applies the algorithm to an ExpansionSequent by compressing and decompressing.
   * @param sequent The ExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: ExpansionSequent, prover: Prover )( implicit dummyImplicit: DummyImplicit ): Seq[ExpansionSequent] =
    apply( compressQuantifiers( sequent ), prover ).map( decompressQuantifiers.apply )
}

/**
 * Given an expansion sequent S, this algorithm computes a single expansion
 * sequents below S that is valid and minimal. This algorithm is considerably
 * faster than the one implemented in minimalExpansionSequents.
 */
object minimalExpansionSequent {
  /**
   * Applies the algorithm to a MultiExpansionSequent.
   * @param sequent The MultiExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: MultiExpansionSequent, prover: Prover ): Option[MultiExpansionSequent] =
    new Minimizer( sequent, prover ).computeAMinimal()

  /**
   * Applies the algorithm to an ExpansionSequent by compressing and decompressing.
   * @param sequent The ExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: ExpansionSequent, prover: Prover )( implicit dummyImplicit: DummyImplicit ): Option[ExpansionSequent] =
    apply( compressQuantifiers( sequent ), prover ).map( decompressQuantifiers.apply )
}

/**
 * Class for computing expansion sequents below S that are valid and minimal.
 * @param sequent The MultiExpansionSequent to be evaluated.
 * @param prover The prover used for the evaluation.
 */
private[expansionTrees] class Minimizer( val sequent: MultiExpansionSequent, val prover: Prover ) extends Logger {

  val maxRemovedInstance = new mMap[MultiExpansionSequent, Int] // This assigns to each MultiExpansionSequent S the maximum of all numbers n with the following property: S can be obtained from a MultiExpansionSequent S' by removing the nth instance of S'.

  /**
   * Compute the list of all minimal expansion sequents below sequent.
   * @return A sequence of minimal expansion sequents.
   */
  def computeAllMinimal(): Seq[MultiExpansionSequent] = {
    val result = new ListBuffer[MultiExpansionSequent] // The list of minimal expansion proofs will be constructed iteratively.
    val stack = new scala.collection.mutable.Stack[MultiExpansionSequent] // Invariant: the stack only contains valid expansion sequents.

    if ( prover.isValid( sequent.toDeep ) ) {
      debug( "The starting sequent is tautological." )
      stack.push( sequent ) // The sequent under consideration is placed on the stack if it is valid.
      maxRemovedInstance += ( ( sequent, 0 ) ) // The input sequent is assigned number 0 to denote that no instances at all have been removed from it.
    }

    while ( stack.nonEmpty ) {
      debug( "Retrieving sequent from stack" )
      val ( current ) = stack.pop() // Topmost element of stack is retrieved. We already know it is tautological; only need to consider its successors.
      trace( "Retrieved sequent " + current + "." )
      val n = maxRemovedInstance( current )
      trace( "Generating successors" )
      val newSequents = generateSuccessors( current ) // All successor expansion sequents are generated.
      val m = newSequents.length
      trace( m + " successors generated" )
      var minimal = true // We assume that the current sequent is minimal unless we find a counterexample.

      for ( i <- 1 to m ) { // Iterate over the generated successors
        val s = newSequents( i - 1 )
        trace( "Testing validity [" + i + "/" + m + "] ..." )
        if ( prover.isValid( s.toDeep ) ) {
          if ( i >= n ) // This is the core of the optimization: Avoid pushing sequents on the stack multiple times.
            stack.push( s ) // Push valid sequents on the stack

          minimal = false // If there is a valid sequent below the current one, it is not minimal.
        }
      }

      if ( minimal ) {
        debug( "Sequent is minimal." )
        result += current // If the current sequent is minimal, we add it to the results.
      } else {
        debug( "Sequent is not minimal." )
      }
    }

    result.toSeq
  }

  /**
   * Compute a single minimal expansion sequent below sequent.
   * @return a minimal expansion sequent, or None if sequent is not valid.
   */
  def computeAMinimal(): Option[MultiExpansionSequent] = {
    if ( prover.isValid( sequent.toDeep ) )
      Some( computeAMinimal_( sequent ) )
    else
      None
  }

  /**
   * Compute a single minimal expansion sequent below mes. Assumes that
   * mes.toDeep is valid.
   *
   * @param mes the MultiExpansionSequent to be evaluated.
   * @return a minimal expansion sequent.
   */
  private def computeAMinimal_( mes: MultiExpansionSequent ): MultiExpansionSequent = {
    debug( "Minimizing a MultiExpansionSequent with " + getStatistics( mes ).total + " instances..." )
    val suc_opt = generateSuccessors( mes ).find( { s => prover.isValid( s.toDeep ) } )
    if ( suc_opt.isDefined )
      computeAMinimal_( suc_opt.get )
    else
      mes
  }

  /**
   * Given a MultiExpansionSequent, this generates all sequents obtained by removing one instance from one tree.
   * It also updates the maxRemovedInstance map.
   * @param sequent The expansion sequent under consideration.
   * @return A sequence containing all one-instance successors.
   */
  def generateSuccessors( sequent: MultiExpansionSequent ): Seq[MultiExpansionSequent] = sequent match {
    case MultiExpansionSequent( ant, suc ) =>
      val newSequents = new ListBuffer[MultiExpansionSequent] //newSequents will be the list of expansion sequents obtained from S by removing one instance from one tree of S.
      var instanceCounter = 0 // Counts the instances of all trees in the sequent.

      // Loop over the antecedent.
      var n = ant.length
      trace( "Generating successor trees for antecedent ..." )
      for ( j <- 1 to n ) {
        val ( fst, tree +: snd ) = ant.splitAt( j - 1 ) //We iteratively focus each expansion tree in the antecedent of S.
        trace( "[" + j + "/" + n + "]" )
        val newTrees = generateSuccessorTrees( tree ) // We generate all successor trees of the current tree.

        if ( newTrees.isEmpty ) { // This can happen for two reasons: the current tree contains no weak quantifiers or all its weak quantifier nodes have only one instance.
          val newS = MultiExpansionSequent( fst ++ snd, suc ) // Since the current tree only consists of one instance, we form a successor sequent simply by deleting it.
          val k = instanceCounter + 1

          if ( !maxRemovedInstance.contains( newS ) ) // If there is no entry in maxRemovedInstance for newS, we set it to k.
            maxRemovedInstance += newS -> k
          else if ( k > maxRemovedInstance( newS ) ) // We also update the entry for newS if the current value is higher.
            maxRemovedInstance += newS -> k

          newSequents += newS
        } else {
          val instanceNumbers = ( instanceCounter + 1 ) to ( instanceCounter + newTrees.length )

          for ( ( t, k ) <- newTrees zip instanceNumbers ) { // k denotes the instance that was removed from tree in order to produce t.
            val newS = MultiExpansionSequent( fst ++ Seq( t ) ++ snd, suc ) // We combine an expansion tree with the rest of the antecedent and the succedent to produce a new expansion sequent.

            if ( !maxRemovedInstance.contains( newS ) ) // If there is no entry in maxRemovedInstance for newS, we set it to k.
              maxRemovedInstance += newS -> k
            else if ( k > maxRemovedInstance( newS ) ) // We also update the entry for newS if the current value is higher.
              maxRemovedInstance += newS -> k

            newSequents += newS
          }
        }
        instanceCounter += tree.numberOfInstances
      }

      // Loop over the succedent, analogous to the one over the antecedent.
      n = suc.length
      trace( "Generating successor trees for succedent ..." )
      for ( j <- 1 to n ) {
        val ( fst, tree +: snd ) = suc.splitAt( j - 1 )
        trace( "[" + j + "/" + n + "]" )
        val newTrees = generateSuccessorTrees( tree )

        if ( newTrees.isEmpty ) {
          val newS = MultiExpansionSequent( ant, fst ++ snd )
          val k = instanceCounter + 1

          if ( !maxRemovedInstance.contains( newS ) )
            maxRemovedInstance += newS -> k
          else if ( k > maxRemovedInstance( newS ) )
            maxRemovedInstance += newS -> k

          newSequents += newS
        } else {
          val instanceNumbers = ( instanceCounter + 1 ) to ( instanceCounter + newTrees.length )

          for ( ( t, k ) <- newTrees zip instanceNumbers ) {
            val newS = MultiExpansionSequent( ant, fst ++ Seq( t ) ++ snd )

            if ( !maxRemovedInstance.contains( newS ) )
              maxRemovedInstance += newS -> k
            else if ( k > maxRemovedInstance( newS ) )
              maxRemovedInstance += newS -> k

            newSequents += newS
          }
        }
        instanceCounter += tree.numberOfInstances
      }

      newSequents.toSeq
  }

  /**
   * Given a MultiExpansionTree, this produces all trees obtained by erasing exactly one instance.
   * @param tree The tree under consideration.
   * @return All trees that have exactly one fewer instance than the input.
   */
  def generateSuccessorTrees( tree: MultiExpansionTree ): Seq[MultiExpansionTree] = tree match {
    case METAtom( f )      => Nil
    case METWeakening( _ ) => Nil
    case METNeg( s )       => generateSuccessorTrees( s ).map( METNeg.apply )
    case METAnd( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => METAnd( t, right ) ) ++ sRight.map( t => METAnd( left, t ) )
    case METOr( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => METOr( t, right ) ) ++ sRight.map( t => METOr( left, t ) )
    case METImp( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => METImp( t, right ) ) ++ sRight.map( t => METImp( left, t ) )

    case METStrongQuantifier( f, vars, sel ) => generateSuccessorTrees( sel ).map( METStrongQuantifier.apply( f, vars, _ ) )
    case METSkolemQuantifier( f, vars, sel ) => generateSuccessorTrees( sel ).map( METSkolemQuantifier.apply( f, vars, _ ) )

    case METWeakQuantifier( f, inst ) =>
      if ( !inst.head._1.containsWeakQuantifiers ) { //In this case we are in a bottommost weak quantifier node, which means that we will actually remove instances.
        if ( inst.length > 1 ) {
          val instances = listComplements( inst ) //These two lines generate all expansion trees that result from removing an instance from tree.
          instances.map( i => METWeakQuantifier( f, i ) )
        } else Nil
      } else inst.flatMap( p => generateSuccessorTrees( p._1 ) )
  }
}
