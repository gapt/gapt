package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ instantiate, HOLPosition }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import scalaz._
import Scalaz._
import Validation.FlatMap._

case object LogicalAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = {
    val candidates = goal.conclusion.antecedent intersect goal.conclusion.succedent

    candidates match {
      case Seq( formula, _* ) => ( (), LogicalAxiom( formula ) ).success
      case _                  => TacticalFailure( this, Some( goal ), "not a logical axiom" ).failureNel
    }
  }
}

case object TopAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, Top(), _: Suc ) <- findFormula( goal, None ) )
      yield () -> BottomAxiom
}

case object BottomAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, Bottom(), _: Ant ) <- findFormula( goal, None ) )
      yield () -> BottomAxiom
}

case object ReflexivityAxiomTactic extends Tactic[Unit] {
  object Refl {
    def unapply( f: HOLFormula ): Option[LambdaExpression] = f match {
      case Eq( t, t_ ) if t == t_ => Some( t )
      case _                      => None
    }
  }

  def apply( goal: OpenAssumption ) =
    for ( ( _, Refl( t ), _: Suc ) <- findFormula( goal, None ) )
      yield () -> ReflexivityAxiom( t )
}

case object TheoryAxiomTactic extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.conclusion

    if ( goalSequent.forall( _.isInstanceOf[HOLAtom] ) )
      ( (), TheoryAxiom( goalSequent.asInstanceOf[Sequent[HOLAtom]] ) ).success
    else
      TacticalFailure( this, Some( goal ), "not an atomic subgoal" ).failureNel
  }
}

case class NegLeftTactic( applyToLabel: Option[String] = None ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel, Neg( f ), i: Ant ) <- findFormula( goal, applyToLabel )
      newGoal = goal.s.delete( i ) :+ ( existingLabel -> f )
    } yield existingLabel -> NegLeftRule( OpenAssumption( newGoal ), newGoal.indices.last )
}

case class NegRightTactic( applyToLabel: Option[String] = None ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel, Neg( f ), i: Suc ) <- findFormula( goal, applyToLabel )
      newGoal = ( existingLabel -> f ) +: goal.s.delete( i )
    } yield existingLabel -> NegRightRule( OpenAssumption( newGoal ), newGoal.indices.head )
}

case class WeakeningLeftTactic( applyToLabel: String ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, f, i: Ant ) <- findFormula( goal, Some( applyToLabel ) ) )
      yield () -> OpenAssumption( goal.s delete i )
}

case class WeakeningRightTactic( applyToLabel: String ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, f, i: Suc ) <- findFormula( goal, Some( applyToLabel ) ) )
      yield () -> OpenAssumption( goal.s delete i )
}

case class AndLeftTactic( applyToLabel: Option[String] = None ) extends Tactic[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, And( lhs, rhs ), idx: Ant ) <- findFormula( goal, applyToLabel )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.s, label )
      newGoal = ( newLabel1 -> lhs ) +: ( newLabel2 -> rhs ) +: goal.s.delete( idx )
    } yield ( newLabel1, newLabel2 ) -> AndLeftRule( OpenAssumption( newGoal ), Ant( 0 ), Ant( 1 ) )
}

case class AndRightTactic( applyToLabel: Option[String] = None ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, And( lhs, rhs ), idx: Suc ) <- findFormula( goal, applyToLabel ) )
      yield () ->
      AndRightRule( OpenAssumption( goal.s.updated( idx, label -> lhs ) ), idx,
        OpenAssumption( goal.s.updated( idx, label -> rhs ) ), idx )
}

case class OrLeftTactic( applyToLabel: Option[String] = None ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, Or( lhs, rhs ), idx: Ant ) <- findFormula( goal, applyToLabel ) )
      yield () ->
      OrLeftRule( OpenAssumption( goal.s.updated( idx, label -> lhs ) ), idx,
        OpenAssumption( goal.s.updated( idx, label -> rhs ) ), idx )
}

case class OrRightTactic( applyToLabel: Option[String] = None ) extends Tactic[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Or( lhs, rhs ), idx: Suc ) <- findFormula( goal, applyToLabel )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.s, label )
      newGoal = goal.s.delete( idx ) :+ ( newLabel1 -> lhs ) :+ ( newLabel2 -> rhs )
      Seq( rhsIdx, lhsIdx ) = newGoal.indices.reverse.take( 2 )
    } yield ( newLabel1, newLabel2 ) -> OrRightRule( OpenAssumption( newGoal ), lhsIdx, rhsIdx )
}

case class ImpLeftTactic( applyToLabel: Option[String] = None ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, Imp( lhs, rhs ), idx: Ant ) <- findFormula( goal, applyToLabel ) )
      yield () ->
      ImpLeftRule( OpenAssumption( goal.s.delete( idx ) :+ ( label -> lhs ) ), Suc( goal.s.succedent.size ),
        OpenAssumption( goal.s.updated( idx, label -> rhs ) ), idx )
}

case class ImpRightTactic( applyToLabel: Option[String] = None ) extends Tactic[( String, String )] {
  // TODO: keep label for rhs?
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Imp( lhs, rhs ), idx: Suc ) <- findFormula( goal, applyToLabel )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.s, label )
      newGoal = ( newLabel1 -> lhs ) +: goal.s.updated( idx, newLabel2 -> rhs )
    } yield ( newLabel1, newLabel2 ) -> ImpRightRule( OpenAssumption( newGoal ), Ant( 0 ), idx )
}

abstract class StrongQuantTactic extends Tactic[Var] {
  def eigenVariable: Option[Var]
  protected def pickEigenvariable( bound: Var, goal: OpenAssumption ) =
    eigenVariable match {
      case Some( ev ) =>
        if ( freeVariables( goal.conclusion ) contains ev )
          TacticalFailure( this, Some( goal ), "provided eigenvariable would violate eigenvariable condition" ).failureNel
        else
          ev.success
      case None =>
        rename( bound, freeVariables( goal.conclusion ).toList ).success
    }
}

case class ExistsLeftTactic( eigenVariable: Option[Var] = None, applyToLabel: Option[String] = None ) extends StrongQuantTactic {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ Ex( bound, _ ), idx: Ant ) <- findFormula( goal, applyToLabel )
      ev <- pickEigenvariable( bound, goal )
    } yield ev -> ExistsLeftRule( OpenAssumption( goal.s.updated( idx, label -> instantiate( f, ev ) ) ), f, ev )
}

case class ExistsRightTactic( term: LambdaExpression, applyToLabel: Option[String] = None ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ Ex( _, _ ), idx: Suc ) <- findFormula( goal, applyToLabel )
      newLabel = NewLabel( goal.s, label )
    } yield newLabel ->
      ExistsRightRule( OpenAssumption( goal.s :+ ( newLabel -> instantiate( f, term ) ) ), f, term )
}

case class ForallLeftTactic( term: LambdaExpression, applyToLabel: Option[String] = None ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ All( _, _ ), idx: Ant ) <- findFormula( goal, applyToLabel )
      newLabel = NewLabel( goal.s, label )
    } yield newLabel ->
      ForallLeftRule( OpenAssumption( ( newLabel -> instantiate( f, term ) ) +: goal.s ), f, term )
}

case class ForallRightTactic( eigenVariable: Option[Var] = None, applyToLabel: Option[String] = None ) extends StrongQuantTactic {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ All( bound, _ ), idx: Suc ) <- findFormula( goal, applyToLabel )
      ev <- pickEigenvariable( bound, goal )
    } yield ev -> ForallRightRule( OpenAssumption( goal.s.updated( idx, label -> instantiate( f, ev ) ) ), f, ev )
}

case class CutTactic( cutFormula: HOLFormula, cutLabel: String ) extends Tactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val leftPremise = OpenAssumption( goalSequent :+ ( cutLabel, cutFormula ) )
    val rightPremise = OpenAssumption( ( cutLabel, cutFormula ) +: goalSequent )

    val auxProof = CutRule( leftPremise, Suc( leftPremise.s.succedent.length - 1 ), rightPremise, Ant( 0 ) )
    ( () -> auxProof ).success
  }
}

case class EqualityLeftTactic( equalityLabel: String, formulaLabel: String, leftToRight: Option[Boolean] = None, targetFormula: Option[HOLFormula] = None ) extends Tactic[Unit] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for (
      ( ( `equalityLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.antecedent
    ) yield ( eqIndex, formulaIndex )

    indices.headOption match {
      case None => TacticalFailure( this, Some( goal ), "label not found" ).failureNel
      case Some( ( equalityIndex, formulaIndex ) ) =>
        val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
        val ( _, auxFormula ) = goalSequent( formulaIndex )

        def f( l: List[HOLPosition], h: HOLFormula, r: LambdaExpression ): HOLFormula = l match {
          case x :: xs => f( xs, h.replace( x, r ), r )
          case Nil     => h
        }

        def testValidity( mainFormula: HOLFormula ): Boolean = {
          if ( s == t && auxFormula == mainFormula ) {
            val sAux = auxFormula.find( s )

            if ( sAux.isEmpty )
              false
            else
              true
          } else if ( s == t && auxFormula != mainFormula )
            false
          else if ( s != t && auxFormula == mainFormula )
            false
          else {
            val sAux = auxFormula.find( s )
            val sMain = mainFormula.find( s )

            val tAux = auxFormula.find( t )
            val tMain = mainFormula.find( t )

            if ( sAux.isEmpty && tAux.isEmpty )
              false
            else {
              val tToS = sMain intersect tAux
              val sToT = tMain intersect sAux

              if ( tToS.isEmpty ) {
                val mainNew = sToT.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, t ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else if ( sToT.isEmpty ) {
                val mainNew = tToS.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, s ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else
                false
            }
          }
        }

        val replacement = targetFormula match {
          case Some( mainFormula ) =>
            if ( testValidity( mainFormula ) )
              targetFormula
            else None
          case None =>
            val r = leftToRight match {
              case Some( true ) =>
                f( auxFormula.find( s ), auxFormula, t )
              case Some( false ) =>
                f( auxFormula.find( t ), auxFormula, s )
              case None =>
                auxFormula.find( t ) match {
                  case l if l.length > 0 =>
                    f( l, auxFormula, s )
                  case _ =>
                    f( auxFormula.find( s ), auxFormula, t )
                }
            }

            Option( r )

          case _ => None
        }

        replacement match {
          case Some( x ) if x != auxFormula =>
            val newGoal = goalSequent delete ( formulaIndex ) insertAt ( formulaIndex, ( formulaLabel -> x ) )
            val premise = OpenAssumption( newGoal )

            ( (), EqualityLeftRule( premise, equalityIndex, formulaIndex, auxFormula ) ).success
          case _ => TacticalFailure( this, Some( goal ), "FIXME" ).failureNel
        }
    }
  }

  def fromLeftToRight = new EqualityLeftTactic( equalityLabel, formulaLabel, leftToRight = Some( true ) )

  def fromRightToLeft = new EqualityLeftTactic( equalityLabel, formulaLabel, leftToRight = Some( false ) )

  def to( targetFormula: HOLFormula ) = new EqualityLeftTactic( equalityLabel, formulaLabel, targetFormula = Some( targetFormula ) )
}

case class EqualityRightTactic( equalityLabel: String, formulaLabel: String, leftToRight: Option[Boolean] = None, targetFormula: Option[HOLFormula] = None ) extends Tactic[Unit] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = for (
      ( ( `equalityLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.succedent
    ) yield ( eqIndex, formulaIndex )

    indices.headOption match {
      case None => TacticalFailure( this, Some( goal ), "label not found" ).failureNel
      case Some( ( equalityIndex, formulaIndex ) ) =>
        val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
        val ( _, auxFormula ) = goalSequent( formulaIndex )

        def f( l: List[HOLPosition], h: HOLFormula, r: LambdaExpression ): HOLFormula = l match {
          case x :: xs => f( xs, h.replace( x, r ), r )
          case Nil     => h
        }

        def testValidity( mainFormula: HOLFormula ): Boolean = {
          if ( s == t && auxFormula == mainFormula ) {
            val sAux = auxFormula.find( s )

            if ( sAux.isEmpty )
              false
            else
              true
          } else if ( s == t && auxFormula != mainFormula )
            false
          else if ( s != t && auxFormula == mainFormula )
            false
          else {
            val sAux = auxFormula.find( s )
            val sMain = mainFormula.find( s )

            val tAux = auxFormula.find( t )
            val tMain = mainFormula.find( t )

            if ( sAux.isEmpty && tAux.isEmpty )
              false
            else {
              val tToS = sMain intersect tAux
              val sToT = tMain intersect sAux

              if ( tToS.isEmpty ) {
                val mainNew = sToT.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, t ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else if ( sToT.isEmpty ) {
                val mainNew = tToS.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, s ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else
                false
            }
          }
        }

        val replacement = targetFormula match {
          case Some( mainFormula ) =>
            if ( testValidity( mainFormula ) )
              targetFormula
            else None
          case None =>
            val r = leftToRight match {
              case Some( true ) =>
                f( auxFormula.find( s ), auxFormula, t )
              case Some( false ) =>
                f( auxFormula.find( t ), auxFormula, s )
              case None =>
                auxFormula.find( t ) match {
                  case l if l.length > 0 =>
                    f( l, auxFormula, s )
                  case _ =>
                    f( auxFormula.find( s ), auxFormula, t )
                }
            }

            Option( r )

          case _ => None
        }

        replacement match {
          case Some( x ) if x != auxFormula =>
            val newGoal = goalSequent delete ( formulaIndex ) insertAt ( formulaIndex, ( formulaLabel -> x ) )
            val premise = OpenAssumption( newGoal )
            ( (), EqualityRightRule( premise, equalityIndex, formulaIndex, auxFormula ) ).success
          case _ => TacticalFailure( this, Some( goal ), "FIXME" ).failureNel
        }
    }
  }

  def fromLeftToRight = new EqualityRightTactic( equalityLabel, formulaLabel, leftToRight = Some( true ) )

  def fromRightToLeft = new EqualityRightTactic( equalityLabel, formulaLabel, leftToRight = Some( false ) )

  def to( targetFormula: HOLFormula ) = new EqualityRightTactic( equalityLabel, formulaLabel, targetFormula = Some( targetFormula ) )
}

case class DefinitionLeftTactic( applyToLabel: String, replacement: HOLFormula ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, formula, idx: Ant ) <- findFormula( goal, Some( applyToLabel ) ) )
      yield () -> DefinitionLeftRule( OpenAssumption( goal.s.updated( idx, label -> replacement ) ), idx, formula )
}

case class DefinitionRightTactic( applyToLabel: String, replacement: HOLFormula ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, formula, idx: Suc ) <- findFormula( goal, Some( applyToLabel ) ) )
      yield () -> DefinitionRightRule( OpenAssumption( goal.s.updated( idx, label -> replacement ) ), idx, formula )
}