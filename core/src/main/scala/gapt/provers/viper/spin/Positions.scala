package gapt.provers.viper.spin

import gapt.expr.Const
import gapt.expr.util.constants
import gapt.formats.tip.ConditionalReductionRule

case class Positions( rules: Set[ConditionalReductionRule], allPositions: Map[Const, Positions] ) {
  require( rules.nonEmpty )
  require( rules.forall( _.lhsHead == rules.head.lhsHead ) )

  val lhsHead: Const = rules.head.lhsHead
  val allArgs: Set[Int] = rules.head.allArgs

  // An argument is only passive if it is passive locally in every rule.
  // This is because we might have goals with primary positions under non-recursive functions.
  // A neater option might be to use Option's instead and make the distinction at each use site.
  val passiveArgs: Set[Int] = {
    val defined = rules.flatMap( _.passiveArgs( allPositions ) )
    defined.headOption match {
      case None         => Set()
      case Some( args ) => defined.foldLeft( args )( ( acc, pass ) => acc intersect pass )
    }
  }

  // An argument is an accumulator globally if it is so locally
  val accumulatorArgs: Set[Int] = {
    val defined = rules.flatMap( _.accumulatorArgs( allPositions ) )
    defined.headOption match {
      case None         => Set()
      case Some( args ) => defined.foldLeft( args )( ( acc, pass ) => acc intersect pass )
    }
  }

  // An argument is primary otherwise
  val primaryArgs: Set[Int] =
    ( allArgs -- passiveArgs ) -- accumulatorArgs

}

object Positions {
  // TODO: this should maybe be private
  def apply( rules: Set[ConditionalReductionRule], c: Const, allPositions: Map[Const, Positions] ): Option[Positions] = {
    val rs = rules.filter( _.lhsHead == c )
    if ( rs.isEmpty )
      None
    else
      Some( Positions( rs, allPositions ) )
  }

  def splitRules( rules: Set[ConditionalReductionRule] ): Map[Const, Positions] = {
    var allPositions = Map.empty[Const, Positions]
    val symbols = rules.map( _.lhsHead )

    var groups = rules.groupBy( _.lhsHead )

    while ( groups.nonEmpty ) {
      // Find a group of rules where all conditional rules have been processed already.
      // We need this order to process conditionals correctly.
      val next = groups.find {
        case ( _, group ) =>
          group.forall { rule =>
            var usedRules = rule.conditions.flatMap( constants( _ ) ).toSet.union( constants( rule.rhs ) ).intersect( symbols )
            usedRules -= rule.lhsHead
            usedRules.forall( allPositions.isDefinedAt )
          }
      }

      next match {
        case Some( ( c, ruleGroup ) ) =>
          allPositions += c -> Positions( ruleGroup, allPositions )
          groups -= c
        case None =>
          val calls = groups.mapValues( rules =>
            rules.flatMap( rule => constants( rule.rhs ) ++ rule.conditions.flatMap( constants( _ ) ) ) )

          val independent = calls.filterKeys( c => calls.forall { case ( d, fs ) => c == d || !fs.contains( c ) } )
          val mutual = groups -- independent.keys

          // Map mutually inductive calls to null. Currently we treat every argument as primary in this case.
          mutual foreach { case ( c, _ ) => allPositions += c -> null }
          mutual foreach {
            case ( c, ruleGroup ) =>
              allPositions += c -> Positions( ruleGroup, allPositions )
              groups -= c
          }
      }

    }

    allPositions
  }
}
