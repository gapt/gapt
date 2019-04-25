package gapt.expr

import gapt.expr.hol.universalClosure
import gapt.proofs.context.{ Context, State }
import gapt.proofs.context.update.Update
import gapt.proofs.context.facet.Reductions

import scala.annotation.tailrec
import scala.collection.mutable

case class ReductionRule( lhs: Expr, rhs: Expr ) extends Update {
  require( lhs.ty == rhs.ty )
  require(
    freeVariables( rhs ).subsetOf( freeVariables( lhs ) ),
    s"Right-hand side of rule contains variables ${
      freeVariables( rhs ) -- freeVariables( lhs ) mkString ", "
    } which are not in the left hand side:\n"
      + ( lhs === rhs ) )

  override def apply( ctx: Context ): State = {
    ctx.check( lhs )
    ctx.check( rhs )
    ctx.state.update[Reductions]( _ + this )
  }

  val Apps( lhsHead @ Const( lhsHeadName, _, _ ), lhsArgs ) = lhs
  val lhsArgsSize = lhsArgs.size

  val isNonLinear: Boolean = {
    val seen = mutable.Set[Var]()
    def go( e: Expr ): Boolean =
      e match {
        case App( a, b )      => go( a ) || go( b )
        case Abs( _, _ )      => true
        case Const( _, _, _ ) => false
        case v: Var =>
          seen( v ) || { seen += v; false }
      }
    go( lhs )
  }

  val nonVarArgs: Set[Int] =
    lhsArgs.zipWithIndex.filterNot( _._1.isInstanceOf[Var] ).map( _._2 ).toSet

  val structuralRecArgs: Set[Int] =
    lhsArgs.zipWithIndex.collect {
      case ( Apps( _: Const, vs ), i ) if vs.forall( _.isInstanceOf[Var] ) =>
        i
    }.toSet

  val normalizeArgs: Set[Int] =
    if ( isNonLinear ) lhsArgs.indices.toSet else nonVarArgs -- structuralRecArgs

  val whnfArgs: Set[Int] =
    structuralRecArgs -- normalizeArgs

  val allArgs: Set[Int] = lhsArgs.zipWithIndex.map( _._2 ).toSet

  val passiveArgs: Option[Set[Int]] = {
    def go( e: Expr ): Option[Set[Int]] =
      e match {
        case Apps( f, rhsArgs ) if f == lhsHead =>
          val args = lhsArgs.zip( rhsArgs ).zipWithIndex collect {
            case ( ( l, r ), i ) if l == r => i
          }
          Some( args.toSet )
        case App( a, b ) =>
          go( a ) match {
            case None         => go( b )
            case Some( args ) => Some( args.intersect( go( b ).getOrElse( allArgs ) ) )
          }
        case _ => None
      }

    go( rhs )
  }

  val accumulatorArgs: Option[Set[Int]] =
    passiveArgs.map( passive => lhsArgs.zipWithIndex.collect { case ( e, i ) if e.isInstanceOf[Var] => i }.toSet -- passive )

  val primaryArgs: Option[Set[Int]] =
    passiveArgs.flatMap( passive => accumulatorArgs.map( accumulator => ( allArgs -- accumulator ) -- passive ) )

}
object ReductionRule {
  implicit def apply( rule: ( Expr, Expr ) ): ReductionRule =
    ReductionRule( rule._1, rule._2 )

  implicit def apply( atom: Formula ): ReductionRule = {
    val Eq( lhs, rhs ) = atom
    ReductionRule( lhs, rhs )
  }
}

// TODO: maybe belongs in a different file
case class Positions( rules: Set[ReductionRule] ) {
  require( rules.nonEmpty )
  require( rules.forall( _.lhsHead == rules.head.lhsHead ) )

  val lhsHead: Const = rules.head.lhsHead
  val allArgs: Set[Int] = rules.head.allArgs

  private def intersectArgs( rules: Set[ReductionRule], f: ReductionRule => Option[Set[Int]] ): Set[Int] =
    rules.foldLeft( allArgs )( ( args, rule ) => args.intersect( f( rule ).getOrElse( allArgs ) ) )

  val passiveArgs: Set[Int] =
    intersectArgs( rules, _.passiveArgs )

  val accumulatorArgs: Set[Int] =
    intersectArgs( rules, _.accumulatorArgs )

  val primaryArgs: Set[Int] =
    intersectArgs( rules, _.primaryArgs )
}
object Positions {
  def apply( rules: Set[ReductionRule], c: Const ): Option[Positions] = {
    val rs = rules.filter( _.lhsHead == c )
    if ( rs.isEmpty )
      None
    else
      Some( Positions( rs ) )
  }

  def splitRules( rules: Set[ReductionRule] ): Map[Const, Positions] =
    rules.map( r => r.lhsHead -> Positions( rules, r.lhsHead ).get ).toMap
}

case class Normalizer( rules: Set[ReductionRule] ) {
  val headMap = Map() ++ rules.groupBy( _.lhsHeadName ).mapValues { rs =>
    val normalizeArgs = rs.flatMap( _.normalizeArgs )
    val whnfArgs = rs.flatMap( _.whnfArgs ) -- normalizeArgs
    ( rs, whnfArgs, normalizeArgs )
  }

  def +( rule: ReductionRule ): Normalizer =
    Normalizer( rules + rule )

  def toFormula = And( rules.map { case ReductionRule( lhs, rhs ) => universalClosure( lhs === rhs ) } )

  def normalize( expr: Expr ): Expr = {
    val Apps( hd_, as_ ) = whnf( expr )
    Apps( hd_ match {
      case Abs.Block( xs, e ) if xs.nonEmpty =>
        Abs.Block( xs, normalize( e ) )
      case _ => hd_
    }, as_.map( normalize ) )
  }

  @tailrec
  final def whnf( expr: Expr ): Expr =
    reduce1( expr ) match {
      case Some( expr_ ) => whnf( expr_ )
      case None          => expr
    }

  def reduce1( expr: Expr ): Option[Expr] = {
    val Apps( hd, as ) = expr
    hd match {
      case Abs.Block( vs, hd_ ) if vs.nonEmpty && as.nonEmpty =>
        val n = math.min( as.size, vs.size )
        Some( Apps( Substitution( vs.take( n ) zip as.take( n ) )( Abs.Block( vs.drop( n ), hd_ ) ), as.drop( n ) ) )
      case hd @ Const( c, _, _ ) =>
        headMap.get( c ).flatMap {
          case ( rs, whnfArgs, normalizeArgs ) =>
            val as_ = as.zipWithIndex.map {
              case ( a, i ) if whnfArgs( i )      => whnf( a )
              case ( a, i ) if normalizeArgs( i ) => normalize( a )
              case ( a, _ )                       => a
            }
            rs.view.flatMap { r =>
              syntacticMatching( r.lhs, Apps( hd, as_.take( r.lhsArgsSize ) ) ).map { subst =>
                Apps( subst( r.rhs ), as_.drop( r.lhsArgsSize ) )
              }
            }.headOption
        }
      case _ =>
        None
    }
  }

  def isDefEq( a: Expr, b: Expr ): Boolean =
    normalize( a ) == normalize( b )
}

object Normalizer {
  def apply( rules: Traversable[ReductionRule] ): Normalizer =
    Normalizer( rules.toSet )

  def apply( rules: ReductionRule* ): Normalizer =
    Normalizer( rules )
}

object normalize {
  def apply( expr: Expr )( implicit ctx: Context = null ): Expr =
    if ( ctx == null ) BetaReduction.normalize( expr )
    else ctx.normalizer.normalize( expr )
}

object BetaReduction extends Normalizer( Set() ) {
  def betaNormalize( expression: Expr ): Expr =
    normalize( expression )

  def betaNormalize( f: Formula ): Formula =
    betaNormalize( f: Expr ).asInstanceOf[Formula]
}
