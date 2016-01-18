package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic.{ OpenAssumption, Tactic }
import at.logic.gapt.proofs.lk._

/**
 * LogicalAxiom tactic
 * @param label
 */
case class LogicalAxiomTactic( label: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = label match {
      case Some( l1 ) =>
        for {
          ( ( `l1`, a ), indexAnt ) <- goalSequent.zipWithIndex.succedent
          ( ( _, b ), indexSuc ) <- goalSequent.zipWithIndex.antecedent if a == b
        } yield ( indexAnt, indexSuc )

      case None =>
        for {
          ( ( _, a ), indexAnt ) <- goalSequent.zipWithIndex.succedent
          ( ( _, b ), indexSuc ) <- goalSequent.zipWithIndex.antecedent if a == b
        } yield ( indexAnt, indexSuc )
    }

    for ( ( i, _ ) <- indices.headOption ) yield {
      val ax = LogicalAxiom( goalSequent( i )._2 )

      WeakeningMacroRule( ax, goal.conclusion )
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
 * TheoryAxiom tactic
 */
case object TheoryAxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    if ( goalSequent.forall( _.isInstanceOf[HOLAtom] ) )
      Option( TheoryAxiom( goalSequent.asInstanceOf[Sequent[HOLAtom]] ) )
    else
      None
  }

}

/**
 * Tactic for identification of (all) axioms
 */
case object AxiomTactic extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val x = TopAxiomTactic orElse BottomAxiomTactic orElse ReflexivityAxiomTactic orElse LogicalAxiomTactic()
    x( goal )
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
      for (
        ( ( `applyToLabel`, a ), index ) <- goalSequent.zipWithIndex.antecedent;
        ( ( otherLabel, b ), _ ) <- goalSequent.zipWithIndex.antecedent if applyToLabel != otherLabel && a == b
      ) yield index

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
      for (
        ( ( `applyToLabel`, a ), index ) <- goalSequent.zipWithIndex.succedent;
        ( ( otherLabel, b ), _ ) <- goalSequent.zipWithIndex.succedent if applyToLabel != otherLabel && a == b
      ) yield index

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
            rename( v, freeVariables( goal.conclusion ).toList )
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
            rename( v, freeVariables( goal.conclusion ).toList )
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

/**
 * EqualityLeftRule tactic
 * @param equalityLabel
 * @param formulaLabel
 */
case class EqualityLeftTactic( equalityLabel: String, formulaLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for (
      ( ( `equalityLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.antecedent
    ) yield ( eqIndex, formulaIndex )

    for ( ( equalityIndex, formulaIndex ) <- indices.headOption ) yield {
      val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
      val ( _, mainFormula ) = goalSequent( formulaIndex )

      def f( l: List[HOLPosition], h: HOLFormula, r: LambdaExpression ): HOLFormula = l match {
        case x :: xs => f( xs, h.replace( x, r ), r )
        case Nil     => h
      }

      val replacement = mainFormula.find( t ) match {
        case l if l.length > 0 =>
          f( l, mainFormula, s )
        case _ =>
          f( mainFormula.find( s ), mainFormula, t )
      }

      val newGoal = goalSequent delete ( formulaIndex ) insertAt ( formulaIndex, ( formulaLabel -> replacement ) )

      val premise = OpenAssumption( newGoal )

      EqualityLeftRule( premise, equalityIndex, formulaIndex, mainFormula )
    }
  }
}

/**
 * EqualityLeftRule tactic
 * @param equalityLabel
 * @param formulaLabel
 */
case class EqualityRightTactic( equalityLabel: String, formulaLabel: String ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for (
      ( ( `equalityLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.succedent
    ) yield ( eqIndex, formulaIndex )

    for ( ( equalityIndex, formulaIndex ) <- indices.headOption ) yield {
      val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
      val ( _, mainFormula ) = goalSequent( formulaIndex )

      def f( l: List[HOLPosition], h: HOLFormula, r: LambdaExpression ): HOLFormula = l match {
        case x :: xs => f( xs, h.replace( x, r ), r )
        case Nil     => h
      }

      val replacement = mainFormula.find( t ) match {
        case l if l.length > 0 =>
          f( l, mainFormula, s )
        case _ =>
          f( mainFormula.find( s ), mainFormula, t )
      }

      val newGoal = goalSequent delete ( formulaIndex ) insertAt ( formulaIndex, ( formulaLabel -> replacement ) )

      val premise = OpenAssumption( newGoal )

      EqualityRightRule( premise, equalityIndex, formulaIndex, mainFormula )
    }
  }
}

/**
 * DefinitionLeftRule tactic
 * @param applyToLabel
 * @param replacement
 */
case class DefinitionLeftTactic( applyToLabel: String, replacement: HOLFormula ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.antecedent )
        yield index

    for ( i <- indices.headOption ) yield {
      val ( _, existingFormula ) = goalSequent( i )
      val premise = OpenAssumption( goalSequent delete ( i ) insertAt ( i, ( applyToLabel -> replacement ) ) )
      DefinitionLeftRule( premise, i, existingFormula )
    }
  }
}

/**
 * DefinitionRightRule tactic
 * @param applyToLabel
 * @param replacement
 */
case class DefinitionRightTactic( applyToLabel: String, replacement: HOLFormula ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices =
      for ( ( ( `applyToLabel`, _ ), index ) <- goalSequent.zipWithIndex.succedent )
        yield index

    for ( i <- indices.headOption ) yield {
      val ( _, existingFormula ) = goalSequent( i )
      val premise = OpenAssumption( goalSequent delete ( i ) insertAt ( i, ( applyToLabel -> replacement ) ) )
      DefinitionRightRule( premise, i, existingFormula )
    }
  }
}