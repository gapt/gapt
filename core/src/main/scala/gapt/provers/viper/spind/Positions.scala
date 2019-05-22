package gapt.provers.viper.spind

import gapt.expr.Const
import gapt.expr.util.constants
import gapt.formats.tip.ConditionalReductionRule

case class Positions( rules: Set[ConditionalReductionRule], allPositions: Map[Const, Positions] ) {
  require( rules.nonEmpty )
  require( rules.forall( _.lhsHead == rules.head.lhsHead ) )

  val lhsHead: Const = rules.head.lhsHead
  val allArgs: Set[Int] = rules.head.allArgs

  // Intersection of the different argument types, taking reduction rules without recursive calls into account
  // by having them not restrict their arguments to any specific type.
  private def intersectArgs( rules: Set[ConditionalReductionRule], f: ConditionalReductionRule => Option[Set[Int]] ): Set[Int] =
    rules.foldLeft( allArgs )( ( args, rule ) => args.intersect( f( rule ).getOrElse( allArgs ) ) )

  // TODO: these argument positions are a mess

  val primaryArgs: Set[Int] =
    rules.foldLeft( Set.empty[Int] )( ( args, rule ) => args.union( rule.primaryArgs( allPositions ).getOrElse( Set() ) ) )

  val accumulatorArgs: Set[Int] =
    intersectArgs( rules, _.accumulatorArgs( allPositions ) ) -- primaryArgs

  val passiveArgs: Set[Int] =
    ( intersectArgs( rules, _.passiveArgs( allPositions ) ) -- primaryArgs ) -- accumulatorArgs
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
      // NOTE: This does not support mutually defined rules.

      val Some( ( c, ruleGroup ) ) = groups.find {
        case ( _, group ) =>
          group.forall { rule =>
            rule.conditions.forall { cond =>
              val usedRules = constants( cond ).intersect( symbols )
              usedRules.forall( allPositions.isDefinedAt )
            }
          }
      }

      allPositions += c -> Positions( ruleGroup, allPositions )
      groups -= c
    }

    allPositions
  }
}
