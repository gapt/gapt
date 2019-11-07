package gapt.provers.viper.spin

import gapt.expr.util.ConditionalReductionRule
import gapt.expr.{ App, Apps, Const, Expr, Var }
import gapt.expr.util.{ constants, variables }

case class Positions( rules: Set[ConditionalReductionRule], allPositions: Map[Const, Positions] ) {
  require( rules.nonEmpty )
  require( rules.forall( _.lhsHead == rules.head.lhsHead ) )

  val lhsHead: Const = rules.head.lhsHead
  val allArgs: Set[Int] = Positions.allArgs( rules.head )

  // An argument is only passive if it is passive locally in every rule.
  // This is because we might have goals with primary positions under non-recursive functions.
  // A neater option might be to use Option's instead and make the distinction at each use site.
  val passiveArgs: Set[Int] = {
    val defined = rules.flatMap( Positions.passiveArgs( _, allPositions ) )
    defined.headOption match {
      case None         => Set()
      case Some( args ) => defined.foldLeft( args )( ( acc, pass ) => acc intersect pass )
    }
  }

  // An argument is an accumulator globally if it is so locally
  val accumulatorArgs: Set[Int] = {
    val defined = rules.flatMap( Positions.accumulatorArgs( _, allPositions ) )
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
  private def apply( rules: Set[ConditionalReductionRule], c: Const, allPositions: Map[Const, Positions] ): Option[Positions] = {
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
          val calls = groups.view.mapValues( rules =>
            rules.flatMap( rule => constants( rule.rhs ) ++ rule.conditions.flatMap( constants( _ ) ) ) ).toMap

          val independent = calls.view.filterKeys( c => calls.forall { case ( d, fs ) => c == d || !fs.contains( c ) } ).toMap
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

  def allArgs( rule: ConditionalReductionRule ): Set[Int] = rule.lhsArgs.zipWithIndex.map( _._2 ).toSet

  // Argument positions that occur only passively or not at all in expr
  def passivesIn( expr: Expr, rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Set[Int] = {
    def go( e: Expr ): Set[Int] =
      e match {
        case Apps( f @ Const( _, _, _ ), rhsArgs ) if allPositions.isDefinedAt( f ) =>
          val poses = allPositions( f )
          val passArgs = if ( poses == null ) Set() else poses.passiveArgs
          val passives = passArgs.map( rhsArgs )
          val passVars = passives.flatMap( variables( _ ) )
          val immediate = rule.lhsArgs.zipWithIndex.collect {
            case ( l, i ) if passVars.intersect( variables( l ) ).nonEmpty => i
          }
          val nested = rhsArgs flatMap go
          immediate.toSet.intersect( nested.toSet )
        case App( a, b ) => go( a ) intersect go( b )
        case _           => allArgs( rule )
      }

    go( expr )
  }

  def primariesIn( expr: Expr, rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Set[Int] = {
    def go( e: Expr ): Set[Int] =
      e match {
        case Apps( f @ Const( _, _, _ ), rhsArgs ) if allPositions.isDefinedAt( f ) =>
          val poses = allPositions( f )
          val primArgs = if ( poses == null ) rhsArgs.zipWithIndex.map( _._2 ).toSet else poses.primaryArgs
          val prims = primArgs.map( rhsArgs )
          val primVars = prims.flatMap( variables( _ ) )
          val immediate = rule.lhsArgs.zipWithIndex.collect {
            case ( l, i ) if primVars.intersect( variables( l ) ).nonEmpty => i
          }
          val nested = prims flatMap go
          immediate.toSet ++ nested
        case App( a, b ) => go( a ) ++ go( b )
        case _           => Set()
      }

    go( expr )
  }

  def conditionalPrimaries( rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Set[Int] =
    rule.conditions.flatMap( cond => primariesIn( cond, rule, allPositions ) ).toSet

  // Positions of arguments which do not change in recursive calls
  // or None if there are no recursive calls on the rhs.
  def selfPassiveArgs( rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Option[Set[Int]] = {
    def go( e: Expr ): Option[Set[Int]] =
      e match {
        case Apps( f, rhsArgs ) if f == rule.lhsHead =>
          val args = rule.lhsArgs.zip( rhsArgs ).zipWithIndex collect {
            case ( ( l, r ), i ) if l == r => i
          }
          Some( args.toSet )
        case App( a, b ) =>
          go( a ) match {
            case None         => go( b )
            case Some( args ) => Some( args.intersect( go( b ).getOrElse( allArgs( rule ) ) ) )
          }
        case _ => None
      }

    go( rule.rhs )
  }

  // Positions of arguments that are self-passive and also passive in calls to other functions.
  def passiveArgs( rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Option[Set[Int]] = {
    val conds = rule.conditions.foldLeft( allArgs( rule ) )( ( acc, cond ) =>
      acc intersect passivesIn( cond, rule, allPositions ) )
    selfPassiveArgs( rule, allPositions ).map( _ intersect conds ).map( _ -- primariesIn( rule.rhs, rule, allPositions ) )
  }

  // Positions of non-passive arguments which are not matched on or None if no recursive calls on the rhs.
  def accumulatorArgs( rule: ConditionalReductionRule, allPositions: Map[Const, Positions] ): Option[Set[Int]] = {
    passiveArgs( rule, allPositions ).map { passives =>
      val own = rule.lhsArgs.zipWithIndex.collect { case ( e, i ) if e.isInstanceOf[Var] => i }.toSet -- passives
      ( own -- primariesIn( rule.rhs, rule, allPositions ) ) -- conditionalPrimaries( rule, allPositions )
    }
  }

}
