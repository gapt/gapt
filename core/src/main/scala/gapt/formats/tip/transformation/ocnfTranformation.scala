package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.util.find
import gapt.formats.tip.util.tipRename
import gapt.formats.tip.util.freeVariables

object tipOcnf {
  def apply( problem: TipSmtProblem ): TipSmtProblem =
    new TipOcnf( problem )()
}

class TipOcnf( problem: TipSmtProblem ) {

  def apply(): TipSmtProblem = {
    val newDefinitions = problem.definitions map { definition =>
      definition match {
        case funDef @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
          funDef.copy( body = tipOcnf( funDef.body ) )
        case goal @ TipSmtGoal( _, _ ) =>
          goal.copy( expr = tipOcnf( goal.expr ) )
        case assertion @ TipSmtAssertion( _, _ ) =>
          assertion.copy( expr = tipOcnf( assertion.expr ) )
        case _ => definition
      }
    }
    TipSmtProblem( newDefinitions )
  }

  private def tipOcnf( expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        ocnfConnective( AndConnective( expr ) )
      case expr @ TipSmtOr( _ ) =>
        ocnfConnective( OrConnective( expr ) )
      case expr @ TipSmtImp( _ ) =>
        ocnfConnective( ImpConnective( expr ) )
      case expr @ TipSmtEq( _ ) =>
        ocnfConnective( EqConnective( expr ) )
      case expr @ TipSmtForall( _, _ ) => ocnfForall( expr )
      case expr @ TipSmtExists( _, _ ) => ocnfExists( expr )
      case expr @ TipSmtIte( _, _, _ ) => ocnfIte( expr )
      case expr @ TipSmtMatch( _, _ )  => ocnfMatch( expr )
      case expr @ TipSmtFun( _, _ ) =>
        ocnfConnective( FunConnective( expr ) )
      case expr @ TipSmtNot( _ ) => ocnfNot( expr )
      case TipSmtIdentifier( _ ) => expression
      case TipSmtTrue            => TipSmtTrue
      case TipSmtFalse           => TipSmtFalse
    }
  }

  private def ocnfNot( expression: TipSmtNot ): TipSmtExpression = {
    val newSubExpression = tipOcnf( expression.expr )
    newSubExpression match {
      case c @ TipSmtIte( _, _, _ ) =>
        val newIfTrue = tipOcnf( TipSmtNot( c.the ) )
        val newIfFalse = tipOcnf( TipSmtNot( c.els ) )
        TipSmtIte( c.cond, newIfTrue, newIfFalse )
      case m @ TipSmtMatch( _, _ ) =>
        val newCases = m.cases map { c =>
          TipSmtCase( c.pattern, tipOcnf( TipSmtNot( c.expr ) ) )
        }
        TipSmtMatch( m.expr, newCases )
      case _ =>
        TipSmtNot( newSubExpression )
    }
  }

  private def ocnfMatch( expression: TipSmtMatch ): TipSmtExpression = {
    val newMatchedExpr = tipOcnf( expression.expr )
    newMatchedExpr match {
      case c @ TipSmtIte( _, _, _ ) =>
        val newIfTrue = tipOcnf( TipSmtMatch( c.the, expression.cases ) )
        val newIfFalse = tipOcnf( TipSmtMatch( c.els, expression.cases ) )
        TipSmtIte( c.cond, newIfTrue, newIfFalse )
      case m @ TipSmtMatch( _, _ ) =>
        val matchExpr = captureAvoiding( m, Seq( expression ) )
        val newCases = matchExpr.cases map { c =>
          TipSmtCase(
            c.pattern,
            tipOcnf( TipSmtMatch( c.expr, expression.cases ) ) )
        }
        TipSmtMatch( matchExpr.expr, newCases )
      case _ =>
        TipSmtMatch(
          newMatchedExpr,
          expression.cases.map { c =>
            TipSmtCase( c.pattern, tipOcnf( c.expr ) )
          } )
    }
  }

  private def ocnfIte( expression: TipSmtIte ): TipSmtExpression = {
    val newCond = tipOcnf( expression.cond )
    newCond match {
      case c @ TipSmtIte( _, _, _ ) =>
        val newIfTrue = tipOcnf(
          TipSmtIte( c.the, expression.the, expression.els ) )
        val newIfFalse = tipOcnf(
          TipSmtIte( c.els, expression.the, expression.els ) )
        TipSmtIte( c.cond, newIfTrue, newIfFalse )
      case m @ TipSmtMatch( _, _ ) =>
        val matchExpr =
          captureAvoiding( m, Seq( expression.the, expression.els ) )
        val newCases = matchExpr.cases map { c =>
          TipSmtCase(
            c.pattern,
            tipOcnf( TipSmtIte( c.expr, expression.the, expression.els ) ) )
        }
        TipSmtMatch( matchExpr.expr, newCases )
      case _ =>
        TipSmtIte(
          newCond,
          tipOcnf( expression.the ),
          tipOcnf( expression.els ) )
    }
  }

  private def ocnfExists( expression: TipSmtExists ): TipSmtExpression = {
    TipSmtExists( expression.variables, tipOcnf( expression.formula ) )
  }

  private def ocnfForall( expression: TipSmtForall ): TipSmtExpression = {
    TipSmtForall( expression.variables, tipOcnf( expression.formula ) )
  }

  private abstract class Connective(
      val subexpressions: Seq[TipSmtExpression] ) {
    def toExpression: TipSmtExpression
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtExpression
  }
  private case class AndConnective(
      tipSmtAnd: TipSmtAnd ) extends Connective( tipSmtAnd.exprs ) {
    def toExpression = TipSmtAnd( subexpressions )
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtAnd =
      TipSmtAnd( subexpressions )
  }
  private case class OrConnective(
      tipSmtOr: TipSmtOr ) extends Connective( tipSmtOr.exprs ) {
    def toExpression = TipSmtOr( subexpressions )
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtOr =
      TipSmtOr( subexpressions )
  }
  private case class ImpConnective(
      tipSmtImp: TipSmtImp ) extends Connective( tipSmtImp.exprs ) {
    def toExpression = TipSmtImp( subexpressions )
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtImp =
      TipSmtImp( subexpressions )
  }
  private case class EqConnective(
      tipSmtEq: TipSmtEq ) extends Connective( tipSmtEq.exprs ) {
    def toExpression = TipSmtEq( subexpressions )
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtEq =
      TipSmtEq( subexpressions )
  }
  private case class FunConnective(
      tipSmtFun: TipSmtFun ) extends Connective( tipSmtFun.arguments ) {
    def toExpression = TipSmtFun( tipSmtFun.name, subexpressions )
    def copy( subexpressions: Seq[TipSmtExpression] ): TipSmtFun =
      tipSmtFun.copy( arguments = subexpressions )
  }

  private def ocnfConnective( connective: Connective ): TipSmtExpression = {
    val newSubExpressions = connective.subexpressions map tipOcnf
    if ( newSubExpressions.exists( _.isInstanceOf[TipSmtIte] ) ) {
      ocnfConnectiveIte( connective, newSubExpressions )
    } else if ( newSubExpressions.exists( _.isInstanceOf[TipSmtMatch] ) ) {
      ocnfConnectiveMatch( connective, newSubExpressions )
    } else {
      connective.copy( connective.subexpressions.map( tipOcnf ) )
    }
  }

  private def ocnfConnectiveIte(
    connective:        Connective,
    newSubExpressions: Seq[TipSmtExpression] ): TipSmtExpression = {
    val Some( ( left, ite, right ) ) =
      find(
        newSubExpressions,
        { expr: TipSmtExpression => expr.isInstanceOf[TipSmtIte] } )

    val TipSmtIte( cond, ifTrue, ifFalse ) = ite
    val newIfTrue = connective.copy( left ++ Seq( ifTrue ) ++ right )
    val newIfFalse = connective.copy( left ++ Seq( ifFalse ) ++ right )
    TipSmtIte( cond, tipOcnf( newIfTrue ), tipOcnf( newIfFalse ) )
  }

  private def ocnfConnectiveMatch(
    connective:        Connective,
    newSubExpressions: Seq[TipSmtExpression] ): TipSmtExpression = {
    val Some( ( left, m, right ) ) =
      find(
        newSubExpressions,
        { expr: TipSmtExpression => expr.isInstanceOf[TipSmtMatch] } )
    val matchExpr =
      captureAvoiding( m.asInstanceOf[TipSmtMatch], left ++ right )
    val TipSmtMatch( matchedTerm, cases ) = matchExpr
    val newCases = cases map {
      cas =>
        TipSmtCase(
          cas.pattern,
          tipOcnf( connective.copy( left ++ Seq( cas.expr ) ++ right ) ) )
    }
    TipSmtMatch( matchedTerm, newCases )
  }

  private def captureAvoiding(
    tipSmtMatch: TipSmtMatch,
    expressions: Seq[TipSmtExpression] ): TipSmtMatch = {
    val blacklist = expressions.flatMap( freeVariables( problem, _ ) )
    TipSmtMatch( tipSmtMatch.expr, tipSmtMatch.cases map { c =>
      tipRename.awayFrom( c, blacklist )
    } )
  }
}
