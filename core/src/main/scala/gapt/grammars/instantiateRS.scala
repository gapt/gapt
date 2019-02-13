package gapt.grammars

import gapt.expr._
import cats.instances.list._
import cats.syntax.traverse._
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables

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
