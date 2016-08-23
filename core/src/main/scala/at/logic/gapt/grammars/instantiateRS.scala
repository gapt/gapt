package at.logic.gapt.grammars

import scalaz._
import Scalaz._
import at.logic.gapt.expr._

object instantiateRS {

  def apply( recursionScheme: RecursionScheme, terms: Set[LambdaExpression] ): RecursionScheme = {
    val sts = terms.groupBy { _.exptype }.withDefaultValue( Set() )

    recursionScheme.copy( rules = recursionScheme.rules flatMap {
      case rule @ Rule( Apps( nt, args ), rhs ) =>
        for {
          subst <- args.filterNot { _.isInstanceOf[Var] }.flatMap { freeVariables( _ ) }.traverse( v => sts( v.exptype ) map { v -> _ } toList )
        } yield Substitution( subst )( rule )
    } )
  }

}
