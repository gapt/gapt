package gapt.expr

import gapt.expr.hol.universalClosure
import gapt.proofs.Context

import scala.annotation.tailrec
import scala.collection.mutable

case class ReductionRule( lhs: Expr, rhs: Expr ) {
  require( lhs.ty == rhs.ty )
  require(
    freeVariables( rhs ).subsetOf( freeVariables( lhs ) ),
    s"Right-hand side of rule contains variables ${
      freeVariables( rhs ) -- freeVariables( lhs ) mkString ", "
    } which are not in the left hand side:\n"
      + ( lhs === rhs ) )

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
}
object ReductionRule {
  implicit def apply( rule: ( Expr, Expr ) ): ReductionRule =
    ReductionRule( rule._1, rule._2 )

  implicit def apply( atom: Formula ): ReductionRule = {
    val Eq( lhs, rhs ) = atom
    ReductionRule( lhs, rhs )
  }
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

  def replaceTy( ty: Ty, oldTy: Ty, newTy: Ty ): Ty = {
    ty match {
      case ty if ty == oldTy => newTy
      case TArr( tyA, tyB )  => TArr( replaceTy( tyA, oldTy, newTy ), replaceTy( tyB, oldTy, newTy ) )
      case ty                => ty
    }
  }

  // TODO: normalize?
  def commute( block: Expr, appOrArg: Either[Expr, Expr] ): Expr = {
    block match {
      case Apps( Const( "handle", ty, params ), as ) =>
        val newCatchB = appOrArg match {
          case Left( app_ )  => app_( as( 1 ) )
          case Right( arg_ ) => as( 1 )( arg_ )
        }
        val newHandle = Const( "handle", replaceTy( ty, params( 1 ), newCatchB.ty ), params.map( replaceTy( _, params( 1 ), newCatchB.ty ) ) )

        Apps( newHandle, Seq( as( 0 ), newCatchB ) )

      case Abs( v, arg ) =>
        appOrArg match {
          case Left( app_ )  => Abs( v, app_( arg ) )
          case Right( arg_ ) => Abs( v, arg( arg_ ) )
        }
    }
  }

  object SplitEfq {
    def unapply( xs: List[Expr] ): Option[( List[Expr], Expr, List[Expr] )] = {
      val index = xs.indexWhere {
        case Apps( Const( "efq", _, _ ), _ ) => true
        case _                               => false
      }
      if ( index == -1 ) {
        None
      } else {
        val ( front, tc :: back ) = xs.splitAt( index )
        Some( ( front, tc, back ) )
      }
    }
  }
  object SplitTryCatch {
    def unapply( xs: List[Expr] ): Option[( List[Expr], Expr, List[Expr] )] = {
      val index = xs.indexWhere {
        case Apps( Const( "tryCatch", _, _ ), _ ) => true
        case _                                    => false
      }
      if ( index == -1 ) {
        None
      } else {
        val ( front, tc :: back ) = xs.splitAt( index )
        Some( ( front, tc, back ) )
      }
    }
  }

  def normalize( expr: Expr ): Expr =
    whnf( expr ) match {
      case Apps( hd_, as_ ) =>
        as_ match {
          // raise left
          case SplitEfq( _, Apps( Const( "efq", _, params ), as2_ ), _ ) =>
            val newEfq = Const( "efq", TArr( as2_( 0 ).ty, expr.ty ), List( params( 0 ), expr.ty ) )
            normalize( newEfq( as2_( 0 ) ) )
          // Commuting conversion (left) for try/catch
          case SplitTryCatch( front, Apps( Const( "tryCatch", ty, params ), as2_ ), back ) if hd_.toUntypedAsciiString != "handle" =>
            //println( s"input:\n$expr" )
            //println( s"commuting:\n${hd_( front )}" )
            val as2Commuted = as2_.map( commute( _, Left( hd_( front ) ) ) )
            val Abs( _, arg ) = as2Commuted( 0 )
            val res = Apps( Const( "tryCatch", replaceTy( ty, params( 1 ), arg.ty ), params.map( replaceTy( _, params( 1 ), arg.ty ) ) ), as2Commuted ++ back )
            //println( s"left: res:\n$res" )
            normalize( res )
          case _ =>
            Apps( hd_ match {
              case Abs.Block( xs, e ) if xs.nonEmpty =>
                Abs.Block( xs, normalize( e ) )
              case _ =>
                hd_
            }, as_.map( normalize ) )
        }
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
      // raise right
      case hd @ Const( "efq", _, _ ) if as.size > 1 =>
        Some( normalize( hd( as( 0 ) ) ) )
      case Const( "efq", _, _ ) =>
        None
      // Commuting conversion (right) for try/catch
      case Const( "tryCatch", ty, params ) if as.size >= 3 =>
        //println( s"input:\n$expr" )
        //println( s"commuting:\n${as( 2 )}" )
        val tryB = commute( normalize( as( 0 ) ), Right( normalize( as( 2 ) ) ) )
        val catchB = commute( normalize( as( 1 ) ), Right( normalize( as( 2 ) ) ) )
        val Abs( _, arg ) = tryB
        val res = Apps( Const( "tryCatch", replaceTy( ty, params( 1 ), arg.ty ), params.map( replaceTy( _, params( 1 ), arg.ty ) ) ), List( tryB, catchB ) ++ as.drop( 3 ) )
        //println( s"right: res:\n$res" )
        Some( normalize( res ) )
      case Const( "tryCatch", ty, params ) =>
        val tryB = as( 0 )
        val Abs( exnV, arg ) = tryB
        if ( !freeVariables( arg ).contains( exnV ) ) {
          // handle simp
          Some( arg )
        } else {
          // handle/raise
          println( s"free vars: ${freeVariables( arg )}" )
          None
        }
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
    //}
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
