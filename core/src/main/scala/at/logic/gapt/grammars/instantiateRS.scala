package at.logic.gapt.grammars

import at.logic.gapt.expr._
import cats.instances.list._, cats.syntax.traverse._

object instantiateRS {

  def apply( recursionScheme: RecursionScheme, terms: Set[Expr] ): RecursionScheme = {
    val sts = terms.groupBy { _.ty }.withDefaultValue( Set() )

    recursionScheme.copy( rules = recursionScheme.rules flatMap {
      case rule @ Rule( Apps( nt, args ), rhs ) =>
        args.filterNot { _.isInstanceOf[Var] }.
          flatMap { freeVariables( _ ) }.
          traverse { v => sts( v.ty ).map { v -> _ }.toList }.
          map { Substitution( _ )( rule ) }
    } )
  }

}
