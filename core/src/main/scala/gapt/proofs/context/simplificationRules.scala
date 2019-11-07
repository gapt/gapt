package gapt.proofs.context

import gapt.expr.formula._
import gapt.expr.ty.{ Ti, To }
import gapt.expr.util
import gapt.expr.util.ConditionalReductionRule
import gapt.expr.{ ReductionRule, Var }

// Simple constant simplification and double-negation elimination
object simplificationRules {

  val rules: Set[ReductionRule] = {
    val lhs = Var( "lhs", To )
    val rhs = Var( "rhs", To )
    Set(
      new ReductionRule( Eq( Var( "x", Ti ), Var( "x", Ti ) ), Top() ),

      new ReductionRule( Neg( Top() ), Bottom() ),
      new ReductionRule( Neg( Bottom() ), Top() ),
      new ReductionRule( Neg( Neg( lhs ) ), lhs ),

      new ReductionRule( Or( Top(), rhs ), Top() ),
      new ReductionRule( Or( lhs, Top() ), Top() ),
      new ReductionRule( Or( Bottom(), rhs ), rhs ),
      new ReductionRule( Or( lhs, Bottom() ), lhs ),

      new ReductionRule( And( Top(), rhs ), rhs ),
      new ReductionRule( And( lhs, Top() ), lhs ),
      new ReductionRule( And( Bottom(), rhs ), Bottom() ),
      new ReductionRule( And( lhs, Bottom() ), Bottom() ),

      new ReductionRule( Imp( Top(), rhs ), rhs ),
      new ReductionRule( Imp( lhs, Top() ), Top() ),
      new ReductionRule( Imp( Bottom(), rhs ), Top() ),
      new ReductionRule( Imp( lhs, Bottom() ), Neg( lhs ) ),

      new ReductionRule( Iff( Top(), rhs ), rhs ),
      new ReductionRule( Iff( lhs, Top() ), lhs ),
      new ReductionRule( Iff( Bottom(), rhs ), Neg( rhs ) ),
      new ReductionRule( Iff( lhs, Bottom() ), Neg( lhs ) ) )
  }

  val conditionalRules: Set[ConditionalReductionRule] =
    rules map { case ReductionRule( lhs, rhs ) => util.ConditionalReductionRule( List(), lhs, rhs ) }
}

