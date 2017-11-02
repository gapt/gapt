package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.proofs.{ Context, Sequent }

class extractRecSchem2( var ctx: Context ) {

  def ty( f: Formula, p: Polarity ): Ty =
    ( f, p ) match {
      case ( All( v, g ), Polarity.InAntecedent ) => v.ty ->: ty( g, p )
      case ( Ex( v, g ), Polarity.InSuccedent )   => v.ty ->: ty( g, p )
      case ( All( v, g ), Polarity.InSuccedent )  => ( v.ty ->: ty( g, p ) ->: To ) ->: To
      case ( Ex( v, g ), Polarity.InAntecedent )  => ( v.ty ->: ty( g, p ) ->: To ) ->: To
      case ( _, _ ) if !containsQuantifier( f )   => To
    }

  val plus: Const = rename( hoc"'+': o>o>o", ctx.constants )
  val zero: Const = rename( hoc"0: o", ctx.constants )
  ctx += plus
  ctx += zero

  def sum( es: Iterable[Expr] ): Expr = es.reduceOption( plus( _, _ ) ).getOrElse( zero )
  def sum( es: Expr* ): Expr = sum( es )

  def proof( p: LKProof, args: Sequent[Expr] ): Expr =
    p match {
      case LogicalAxiom( _ ) | ReflexivityAxiom( _ ) => sum( args.elements )
      case TopAxiom | BottomAxiom                    => zero
      case p @ WeakQuantifierRule( q, a, f, t, v, pol ) =>
        proof( q, p.occConnectors.head.parent( args ).updated( a, args( p.mainIndices.head )( t ) ) )
      case p @ StrongQuantifierRule( q, a, ev, qv, pol ) =>
        args( p.mainIndices.head )( Abs( ev, proof( q, ??? ) ) )
      case _ =>
        sum {
          for ( ( q, oc ) <- p.immediateSubProofs zip p.occConnectors )
            yield proof( q, oc.parent( args ) )
        }
    }
}
