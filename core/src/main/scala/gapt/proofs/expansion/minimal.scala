package gapt.proofs.expansion

import gapt.provers.Prover
import gapt.utils.Logger

import scala.collection.mutable

/**
 * Given an expansion sequent S, this algorithm computes the list of expansion
 * sequents below S that are valid and minimal.
 */
object minimalExpansionSequents {
  val logger = minimalExpansionSequent.logger

  /**
   * Applies the algorithm to a ExpansionSequent.
   * @param sequent The ExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: ExpansionSequent, prover: Prover ): Seq[ExpansionSequent] =
    new Minimizer( sequent, prover ).computeAllMinimal()
}

/**
 * Given an expansion sequent S, this algorithm computes a single expansion
 * sequents below S that is valid and minimal. This algorithm is considerably
 * faster than the one implemented in minimalExpansionSequents.
 */
object minimalExpansionSequent {
  val logger = Logger( "minimalExpansionSequent" )

  /**
   * Applies the algorithm to a ExpansionSequent.
   * @param sequent The ExpansionSequent to be evaluated.
   * @param prover The prover used for the evaluation.
   * @return A sequence of minimal expansion sequents.
   */
  def apply( sequent: ExpansionSequent, prover: Prover ): Option[ExpansionSequent] =
    new Minimizer( sequent, prover ).computeAMinimal()

  def apply( proof: ExpansionProof, prover: Prover ): Option[ExpansionProof] =
    apply( proof.expansionSequent, prover ) map { ExpansionProof }
}

/**
 * Class for computing expansion sequents below S that are valid and minimal.
 * @param sequent The ExpansionSequent to be evaluated.
 * @param prover The prover used for the evaluation.
 */
private[expansion] class Minimizer( val sequent: ExpansionSequent, val prover: Prover ) {
  import minimalExpansionSequent.logger._

  // This assigns to each ExpansionSequent S the maximum of all numbers n with the following property:
  // S can be obtained from a ExpansionSequent S' by removing the nth instance of S'.
  val maxRemovedInstance: mutable.Map[ExpansionSequent, Int] = mutable.HashMap()

  /**
   * Compute the list of all minimal expansion sequents below sequent.
   * @return A sequence of minimal expansion sequents.
   */
  def computeAllMinimal(): Seq[ExpansionSequent] = {
    // The list of minimal expansion proofs will be constructed iteratively.
    val result = mutable.Buffer[ExpansionSequent]()
    // Invariant: the stack only contains valid expansion sequents.
    val stack = mutable.ArrayStack[ExpansionSequent]()

    if ( prover.isValid( sequent map { _.deep } ) ) {
      debug( "The starting sequent is tautological." )
      stack.push( sequent ) // The sequent under consideration is placed on the stack if it is valid.
      // The input sequent is assigned number 0 to denote that no instances at all have been removed from it.
      maxRemovedInstance += ( ( sequent, 0 ) )
    }

    while ( stack.nonEmpty ) {
      debug( "Retrieving sequent from stack" )
      // Topmost element of stack is retrieved. We already know it is
      // tautological; only need to consider its successors.
      val ( current ) = stack.pop()
      debug( "Retrieved sequent " + current + "." )
      val n = maxRemovedInstance( current )
      debug( "Generating successors" )
      val newSequents = generateSuccessors( current ) // All successor expansion sequents are generated.
      val m = newSequents.length
      debug( m + " successors generated" )
      var minimal = true // We assume that the current sequent is minimal unless we find a counterexample.

      for ( i <- 1 to m ) { // Iterate over the generated successors
        val s = newSequents( i - 1 )
        debug( "Testing validity [" + i + "/" + m + "] ..." )
        if ( prover.isValid( s map { _.deep } ) ) {
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

    result
  }

  /**
   * Compute a single minimal expansion sequent below sequent.
   * @return a minimal expansion sequent, or None if sequent is not valid.
   */
  def computeAMinimal(): Option[ExpansionSequent] = {
    if ( prover.isValid( sequent map { _.deep } ) )
      Some( computeAMinimal_( sequent ) )
    else
      None
  }

  /**
   * Compute a single minimal expansion sequent below mes. Assumes that
   * mes.toDeep is valid.
   *
   * @param mes the ExpansionSequent to be evaluated.
   * @return a minimal expansion sequent.
   */
  private def computeAMinimal_( mes: ExpansionSequent ): ExpansionSequent = {
    debug( "Minimizing an ExpansionSequent with " + numberOfInstancesET( mes ) + " instances..." )
    val suc_opt = generateSuccessors( mes ).find( { s => prover.isValid( s map { _.deep } ) } )
    if ( suc_opt.isDefined )
      computeAMinimal_( suc_opt.get )
    else
      mes
  }

  /**
   * Given a ExpansionSequent, this generates all sequents obtained by removing one instance from one tree.
   * It also updates the maxRemovedInstance map.
   * @param sequent The expansion sequent under consideration.
   * @return A sequence containing all one-instance successors.
   */
  def generateSuccessors( sequent: ExpansionSequent ): Seq[ExpansionSequent] = sequent match {
    case ExpansionSequent( ant, suc ) =>
      // newSequents will be the list of expansion sequents obtained
      // from S by removing one instance from one tree of S.
      val newSequents = mutable.Buffer[ExpansionSequent]()
      var instanceCounter = 0 // Counts the instances of all trees in the sequent.

      // Loop over the antecedent.
      var n = ant.length
      for ( j <- 1 to n ) {
        // We iteratively focus each expansion tree in the antecedent of S.
        val ( fst, tree +: snd ) = ant.splitAt( j - 1 )
        val newTrees = generateSuccessorTrees( tree ) // We generate all successor trees of the current tree.

        if ( newTrees.isEmpty ) {
          // This can happen for two reasons:
          // the current tree contains no weak quantifiers or
          // all its weak quantifier nodes have only one instance.
          val newS = ExpansionSequent( fst ++ snd, suc )
          // Since the current tree only consists of one instance,
          // we form a successor sequent simply by deleting it.
          val k = instanceCounter + 1

          if ( !maxRemovedInstance.contains( newS ) )
            // If there is no entry in maxRemovedInstance for newS, we set it to k.
            maxRemovedInstance += newS -> k
          else if ( k > maxRemovedInstance( newS ) )
            // We also update the entry for newS if the current value is higher.
            maxRemovedInstance += newS -> k

          newSequents += newS
        } else {
          val instanceNumbers = ( instanceCounter + 1 ) to ( instanceCounter + newTrees.length )

          for ( ( t, k ) <- newTrees zip instanceNumbers ) {
            // k denotes the instance that was removed from tree in order to produce t.
            val newS = ExpansionSequent( fst ++ Seq( t ) ++ snd, suc )
            // We combine an expansion tree with the rest of the antecedent and the succedent
            // to produce a new expansion sequent.

            if ( !maxRemovedInstance.contains( newS ) )
              // If there is no entry in maxRemovedInstance for newS, we set it to k.
              maxRemovedInstance += newS -> k
            else if ( k > maxRemovedInstance( newS ) )
              // We also update the entry for newS if the current value is higher.
              maxRemovedInstance += newS -> k

            newSequents += newS
          }
        }
        instanceCounter += numberOfInstancesET( tree )
      }

      // Loop over the succedent, analogous to the one over the antecedent.
      n = suc.length
      for ( j <- 1 to n ) {
        val ( fst, tree +: snd ) = suc.splitAt( j - 1 )
        val newTrees = generateSuccessorTrees( tree )

        if ( newTrees.isEmpty ) {
          val newS = ExpansionSequent( ant, fst ++ snd )
          val k = instanceCounter + 1

          if ( !maxRemovedInstance.contains( newS ) )
            maxRemovedInstance += newS -> k
          else if ( k > maxRemovedInstance( newS ) )
            maxRemovedInstance += newS -> k

          newSequents += newS
        } else {
          val instanceNumbers = ( instanceCounter + 1 ) to ( instanceCounter + newTrees.length )

          for ( ( t, k ) <- newTrees zip instanceNumbers ) {
            val newS = ExpansionSequent( ant, fst ++ Seq( t ) ++ snd )

            if ( !maxRemovedInstance.contains( newS ) )
              maxRemovedInstance += newS -> k
            else if ( k > maxRemovedInstance( newS ) )
              maxRemovedInstance += newS -> k

            newSequents += newS
          }
        }
        instanceCounter += numberOfInstancesET( tree )
      }

      newSequents
  }

  /**
   * Given a ExpansionTree, this produces all trees obtained by erasing exactly one instance.
   * @param tree The tree under consideration.
   * @return All trees that have exactly one fewer instance than the input.
   */
  def generateSuccessorTrees( tree: ExpansionTree ): Seq[ExpansionTree] = tree match {
    case ETAtom( _, _ )      => Nil
    case ETWeakening( _, _ ) => Nil
    case ETTop( _ )          => Nil
    case ETBottom( _ )       => Nil
    case ETDefinition( sh, child ) =>
      generateSuccessorTrees( child ).map( ETDefinition( sh, _ ) )
    case ETNeg( s ) => generateSuccessorTrees( s ).map( ETNeg.apply )
    case ETAnd( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => ETAnd( t, right ) ) ++ sRight.map( t => ETAnd( left, t ) )
    case ETOr( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => ETOr( t, right ) ) ++ sRight.map( t => ETOr( left, t ) )
    case ETImp( left, right ) =>
      val sLeft = generateSuccessorTrees( left )
      val sRight = generateSuccessorTrees( right )
      sLeft.map( t => ETImp( t, right ) ) ++ sRight.map( t => ETImp( left, t ) )

    case ETStrongQuantifier( f, vars, sel ) =>
      generateSuccessorTrees( sel ).map( ETStrongQuantifier.apply( f, vars, _ ) )
    case ETSkolemQuantifier( f, st, sf, sel ) =>
      generateSuccessorTrees( sel ).map( ETSkolemQuantifier.apply( f, st, sf, _ ) )

    case ETWeakQuantifier( f, inst ) =>
      inst.toSeq flatMap {
        case ( term, child ) =>
          val containsWeakQ = child.subProofs exists {
            case ETWeakQuantifier( _, grandkids ) => grandkids.nonEmpty
            case _                                => false
          }
          if ( containsWeakQ ) {
            generateSuccessorTrees( child ) map { succ => ETWeakQuantifier( f, inst.updated( term, succ ) ) }
          } else {
            // In this case we are in a bottommost weak quantifier node,
            // which means that we will actually remove instances.
            Seq( ETWeakQuantifier( f, inst - term ) )
          }
      }
  }
}
