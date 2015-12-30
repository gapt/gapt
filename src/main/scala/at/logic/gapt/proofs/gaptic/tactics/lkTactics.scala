package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic.{ FreshVariable, OpenAssumption, Tactic }
import at.logic.gapt.proofs.lk._

/**
 * LogicalAxiom tactic
 * @param a
 */
case class LogicalAxiomTactic( a: HOLFormula ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    val indices =
      for {
        ( `a`, indexAnt ) <- goalSequent.zipWithIndex.succedent
        ( `a`, indexSuc ) <- goalSequent.zipWithIndex.antecedent
      } yield ( indexAnt, indexSuc )

    for ( _ <- indices.headOption ) yield {

      val ax = LogicalAxiom( a )

      WeakeningMacroRule( ax, goalSequent )
    }
  }

}

/**
 * TopAxiom tactic
 */
case object TopAxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    val indices =
      for {
        ( Top(), index ) <- goalSequent.zipWithIndex.succedent
      } yield index

    for ( _ <- indices.headOption ) yield {

      val ax = TopAxiom

      WeakeningMacroRule( ax, goalSequent )
    }
  }

}

/**
 * BottomAxiom tactic
 */
case object BottomAxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    val indices =
      for {
        ( Bottom(), index ) <- goalSequent.zipWithIndex.antecedent
      } yield index

    for ( _ <- indices.headOption ) yield {

      val ax = BottomAxiom

      WeakeningMacroRule( ax, goalSequent )
    }
  }

}

/**
 * ReflexivityAxiom tactic
 */
case object ReflexivityAxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    val indices =
      for ( ( Eq( lhs: LambdaExpression, rhs: LambdaExpression ), index ) <- goalSequent.zipWithIndex.succedent if lhs == rhs )
        yield index

    for ( i <- indices.headOption ) yield {
      val Eq( lhs, _ ) = goalSequent( i )

      val ax = ReflexivityAxiom( lhs )

      WeakeningMacroRule( ax, goalSequent )
    }
  }

}

/**
 * Tactic for identification of (all) axioms
 */
case object AxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = goal.conclusion match {
    case Sequent( Seq( f: HOLAtom ), Seq( g: HOLAtom ) ) if f == g => LogicalAxiomTactic( f )( goal )
    case Sequent( Seq(), Seq( Top() ) ) => TopAxiomTactic( goal )
    case Sequent( Seq( Bottom() ), Seq() ) => BottomAxiomTactic( goal )
    case Sequent( Seq(), Seq( Eq( s: LambdaExpression, t: LambdaExpression ) ) ) if s == t => ReflexivityAxiomTactic( goal )
    case _ => None
  }

}

/**
 * NegLeftRule tactic
 * @param applyToLabel
 */
case class NegLeftTactic( applyToLabel: Option[String] = None ) extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Neg( _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Neg( _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    for ( i <- indices.headOption ) yield {
      val ( existingLabel, Neg( e ) ) = goalSequent( i )

      val newGoal = ( goalSequent delete i ) :+ ( existingLabel, e )
      val premise = OpenAssumption( newGoal )

      NegLeftRule( premise, Suc( newGoal.succedent.length - 1 ) )
    }
  }
}

/**
 * Companion object for NegRightTactic
 */
object NegLeftTactic {
  def apply( applyToLabel: String ) = new NegLeftTactic( Some( applyToLabel ) )
}

/**
 * NegRightRule tactic
 * @param applyToLabel
 */
case class NegRightTactic( applyToLabel: Option[String] = None ) extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Neg( _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Neg( _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    for ( i <- indices.headOption ) yield {
      val ( existingLabel, Neg( e ) ) = goalSequent( i )

      val newGoal = ( existingLabel, e ) +: ( goalSequent delete i )
      val premise = OpenAssumption( newGoal )

      NegRightRule( premise, Ant( 0 ) )
    }
  }
}

/**
 * Companion object for NegRightTactic
 */
object NegRightTactic {
  def apply( applyToLabel: String ) = new NegRightTactic( Some( applyToLabel ) )
}

/**
 * WeakeningLeftRule tactic
 * @param applyToLabel
 */
case class WeakeningLeftTactic( applyToLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.antecedent )
        yield index

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( _, formula ) = goalSequent( i )

      // New goal with lhs, rhs instead of And(lhs, rhs) in antecedent
      val newGoal = goalSequent.delete( i )

      val premise = OpenAssumption( newGoal )

      WeakeningLeftRule( premise, formula )
    }
  }
}

/**
 * WeakeningRightRule tactic
 * @param applyToLabel
 */
case class WeakeningRightTactic( applyToLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.succedent )
        yield index

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( _, formula ) = goalSequent( i )

      // New goal with lhs, rhs instead of And(lhs, rhs) in antecedent
      val newGoal = goalSequent.delete( i )

      val premise = OpenAssumption( newGoal )

      WeakeningRightRule( premise, formula )
    }
  }
}

/**
 * ContractionLeftRule tactic
 * @param applyToLabel
 */
case class ContractionLeftTactic( applyToLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.antecedent )
        yield index

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, formula ) = goalSequent( i )

      // New goal with lhs, rhs instead of And(lhs, rhs) in antecedent
      val newGoal = goalSequent.delete( i ).insertAt( i, existingLabel + "_1" -> formula ).insertAt( i + 1, existingLabel + "_2" -> formula )

      val firstOccurrenceIndex = Ant( 0 )
      val secondOccurrenceIndex = firstOccurrenceIndex + 1

      val premise = OpenAssumption( newGoal )

      ContractionLeftRule( premise, firstOccurrenceIndex, secondOccurrenceIndex )
    }
  }

}

/**
 * ContractionRightRule tactic
 * @param applyToLabel
 */
case class ContractionRightTactic( applyToLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.succedent )
        yield index

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, formula ) = goalSequent( i )

      // New goal with lhs, rhs instead of And(lhs, rhs) in antecedent
      val newGoal = goalSequent.delete( i ).insertAt( i, existingLabel + "_1" -> formula ).insertAt( i + 1, existingLabel + "_2" -> formula )

      val firstOccurrenceIndex = Suc( newGoal.succedent.length - 2 )
      val secondOccurrenceIndex = firstOccurrenceIndex + 1

      val premise = OpenAssumption( newGoal )

      ContractionRightRule( premise, firstOccurrenceIndex, secondOccurrenceIndex )
    }
  }

}

/**
 * AndLeftRule tactic
 * @param applyToLabel
 */
case class AndLeftTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, And( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, And( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    // Select some formula index!

    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, And( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of And(lhs, rhs) in antecedent
      val newGoal = ( existingLabel + "_1" -> lhs ) +: ( existingLabel + "_2" -> rhs ) +: goalSequent.delete( i )

      // Indices of lhs and rhs
      val lhsIndex = Ant( 0 )
      val rhsIndex = lhsIndex + 1

      val premise = OpenAssumption( newGoal )

      AndLeftRule( premise, lhsIndex, rhsIndex )
    }
  }

}

/**
 * Companion object for AndLeftTactic
 */
object AndLeftTactic {
  def apply( applyToLabel: String ) = new AndLeftTactic( Some( applyToLabel ) )
}

/**
 * AndRightRule tactic
 * @param applyToLabel
 */
case class AndRightTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, And( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, And( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, And( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
      val newGoalLeft = goalSequent.delete( i ).:+( existingLabel -> lhs )
      val newGoalRight = goalSequent.delete( i ).:+( existingLabel -> rhs )

      val premiseLeft = OpenAssumption( newGoalLeft )
      val premiseRight = OpenAssumption( newGoalRight )

      val leftIndex = Suc( newGoalLeft.succedent.length - 1 )
      val rightIndex = Suc( newGoalRight.succedent.length - 1 )

      val lkTmp = AndRightRule( premiseLeft, leftIndex, premiseRight, rightIndex )
      ContractionMacroRule( lkTmp )
    }
  }
}

/**
 * Companion object for AndRightTactic
 */
object AndRightTactic {
  def apply( applyToLabel: String ) = new AndRightTactic( Some( applyToLabel ) )
}

/**
 * OrLeftRule tactic
 * @param applyToLabel
 */
case class OrLeftTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Or( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Or( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, Or( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
      val newGoalLeft = ( existingLabel -> lhs ) +: goalSequent.delete( i )
      val newGoalRight = ( existingLabel -> rhs ) +: goalSequent.delete( i )

      val premiseLeft = OpenAssumption( newGoalLeft )
      val premiseRight = OpenAssumption( newGoalRight )

      val leftIndex = Ant( 0 )
      val rightIndex = Ant( 0 )

      val lkTmp = OrLeftRule( premiseLeft, leftIndex, premiseRight, rightIndex )
      ContractionMacroRule( lkTmp )
    }
  }
}

/**
 * Companion object for OrLeftTactic
 */
object OrLeftTactic {
  def apply( applyToLabel: String ) = new OrLeftTactic( Some( applyToLabel ) )
}

/**
 * OrRightRule tactic
 * @param applyToLabel
 */
case class OrRightTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Or( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Or( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, Or( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
      val newGoal = goalSequent.delete( i ).:+( existingLabel + "_1" -> lhs ).:+( existingLabel + "_2" -> rhs )

      // Indices of lhs and rhs
      val lhsIndex = Suc( newGoal.succedent.length - 2 )
      val rhsIndex = lhsIndex + 1

      val premise = OpenAssumption( newGoal )

      OrRightRule( premise, lhsIndex, rhsIndex )
    }
  }

}

/**
 * Companion object for OrRightTactic
 */
object OrRightTactic {
  def apply( applyToLabel: String ) = new OrRightTactic( Some( applyToLabel ) )
}

/**
 * ImpLeftRule tactic
 * @param applyToLabel
 */
case class ImpLeftTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Imp( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Imp( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, Imp( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
      val newGoalLeft = goalSequent.delete( i ) :+ ( existingLabel -> lhs )
      val newGoalRight = ( existingLabel -> rhs ) +: goalSequent.delete( i )

      val premiseLeft = OpenAssumption( newGoalLeft )
      val premiseRight = OpenAssumption( newGoalRight )

      val leftIndex = Suc( newGoalLeft.succedent.length - 1 )
      val rightIndex = Ant( 0 )

      val lkTmp = ImpLeftRule( premiseLeft, leftIndex, premiseRight, rightIndex )
      ContractionMacroRule( lkTmp )
    }
  }
}

/**
 * Companion object for ImpLeftTactic
 */
object ImpLeftTactic {
  def apply( applyToLabel: String ) = new ImpLeftTactic( Some( applyToLabel ) )
}

/**
 * ImpRightRule tactic
 * @param applyToLabel
 */
case class ImpRightTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Imp( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Imp( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    // Select some formula index!
    for ( i <- indices.headOption ) yield {
      // Extract LHS/RHS
      val ( existingLabel, Imp( lhs, rhs ) ) = goalSequent( i )

      // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
      val newGoal = ( existingLabel + "_1" -> lhs ) +: goalSequent.delete( i ) :+ ( existingLabel + "_2" -> rhs )

      // Indices of lhs and rhs
      val lhsIndex = Ant( 0 )
      val rhsIndex = Suc( newGoal.succedent.length - 1 )

      val premise = OpenAssumption( newGoal )

      ImpRightRule( premise, lhsIndex, rhsIndex )
    }
  }

}

/**
 * Companion object for ImpRightTactic
 */
object ImpRightTactic {
  def apply( applyToLabel: String ) = new ImpRightTactic( Some( applyToLabel ) )
}

/**
 * ExistsLeftRule tactic
 * @param eigenVariable
 * @param applyToLabel
 */
case class ExistsLeftTactic( eigenVariable: Option[Var] = None, applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Ex( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Ex( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    // Select some formula index!
    indices.headOption match {
      case None =>
        None
      case Some( i ) =>
        val ( existingLabel, quantifiedFormula ) = goalSequent( i )
        val Ex( v, fm ) = quantifiedFormula

        val ev = eigenVariable match {
          case Some( x ) => x
          case None =>
            FreshVariable( goal, v )
        }

        if ( freeVariables( goal.conclusion ) contains ev )
          None
        else {
          val auxFormula = Substitution( v, ev )( fm )

          // New goal with instance of fm instead of Exi(v, fm)
          val newGoal = ( existingLabel -> auxFormula ) +: goalSequent.delete( i )

          val premise = OpenAssumption( newGoal )

          Some( ExistsLeftRule( premise, quantifiedFormula, ev ) )
        }
    }
  }

}

/**
 * Companion object for ExistsLeftTactic
 */
object ExistsLeftTactic {
  def apply( eigenVariable: Var, applyToLabel: String ) = new ExistsLeftTactic( Some( eigenVariable ), Some( applyToLabel ) )

  def apply( eigenVariable: Var ) = new ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

  def apply( applyToLabel: String ) = new ExistsLeftTactic( applyToLabel = Some( applyToLabel ) )
}

/**
 * ExistsRightRule tactic
 * @param term
 * @param applyToLabel
 */
case class ExistsRightTactic( term: LambdaExpression, instantiationLabel: String, applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, Ex( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, Ex( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    // Select some formula index!
    if ( goalSequent.find( e => e._1 == instantiationLabel ).isEmpty )
      for ( i <- indices headOption ) yield {
        val ( _, quantifiedFormula ) = goalSequent( i )
        val Ex( v, fm ) = quantifiedFormula

        val auxFormula = Substitution( v, term )( fm )

        val newGoal = goalSequent.insertAt( i, instantiationLabel -> auxFormula )

        val premise = OpenAssumption( newGoal )

        val auxProofSegment = ExistsRightRule( premise, quantifiedFormula, term )

        ContractionRightRule( auxProofSegment, quantifiedFormula )
      }
    else
      None
  }
}

/**
 * Companion object for ExistsRightTactic
 */
object ExistsRightTactic {
  def apply( term: LambdaExpression, instantiationLabel: String, applyToLabel: String ) = new ExistsRightTactic( term, instantiationLabel, Some( applyToLabel ) )
}

/**
 * ForallLeftRule tactic
 * @param term
 * @param applyToLabel
 */
case class ForallLeftTactic( term: LambdaExpression, instantiationLabel: String, applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, All( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, All( _, _ ) ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    if ( goalSequent.find( e => e._1 == instantiationLabel ).isEmpty )
      // Select some formula index!
      for ( i <- indices headOption ) yield {
        val ( _, quantifiedFormula ) = goalSequent( i )
        val All( v, fm ) = quantifiedFormula

        val auxFormula = Substitution( v, term )( fm )

        val newGoal = goalSequent.insertAt( i + 1, instantiationLabel -> auxFormula )

        val premise = OpenAssumption( newGoal )

        val auxProofSegment = ForallLeftRule( premise, quantifiedFormula, term )

        ContractionLeftRule( auxProofSegment, quantifiedFormula )
      }
    else
      None
  }
}

/**
 * Companion object for ForallLeftTactic
 */
object ForallLeftTactic {
  def apply( term: LambdaExpression, instantiationLabel: String, applyToLabel: String ) = new ForallLeftTactic( term, instantiationLabel, Some( applyToLabel ) )
}

/**
 * ForallRightRule tactic
 * @param applyToLabel
 */
case class ForallRightTactic( eigenVariable: Option[Var] = None, applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, All( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, All( _, _ ) ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    // Select some formula index!
    indices.headOption match {
      case None =>
        None
      case Some( i ) =>
        val ( existingLabel, quantifiedFormula ) = goalSequent( i )
        val All( v, fm ) = quantifiedFormula

        val ev = eigenVariable match {
          case Some( x ) => x
          case None =>
            FreshVariable( goal, v )
        }

        if ( freeVariables( goal.conclusion ) contains ev )
          None
        else {
          val auxFormula = Substitution( v, ev )( fm )

          // New goal with instance of fm instead of Exi(v, fm)
          val newGoal = goalSequent.delete( i ) :+ ( existingLabel -> auxFormula )

          val premise = OpenAssumption( newGoal )

          Some( ForallRightRule( premise, quantifiedFormula, ev ) )
        }
    }
  }
}

/**
 * Companion object for ForallRightTactic
 */
object ForallRightTactic {
  def apply( eigenVariable: Var, applyToLabel: String ) = new ForallRightTactic( Some( eigenVariable ), Some( applyToLabel ) )

  def apply( eigenVariable: Var ) = new ForallRightTactic( eigenVariable = Some( eigenVariable ) )

  def apply( applyToLabel: String ) = new ForallRightTactic( applyToLabel = Some( applyToLabel ) )
}

/**
 * CutRule tactic
 * @param cutFormula
 */
case class CutTactic( cutFormula: HOLFormula, cutLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val leftPremise = OpenAssumption( goalSequent :+ ( cutLabel, cutFormula ) )
    val rightPremise = OpenAssumption( ( cutLabel, cutFormula ) +: goalSequent )

    val auxProof = CutRule( leftPremise, Suc( leftPremise.s.succedent.length - 1 ), rightPremise, Ant( 0 ) )
    Some( ContractionMacroRule( auxProof ) )
  }
}

