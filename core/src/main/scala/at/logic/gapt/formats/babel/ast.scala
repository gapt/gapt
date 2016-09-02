package at.logic.gapt.formats.babel

import scalaz._
import Scalaz._
import at.logic.gapt.{ expr => real }

import scala.collection.mutable

/**
 * Intermediate representation for expressions parsed by Babel.
 *
 * This representation is intended to be as simple as possible, all
 * higher-level constructs (such as <-> or ∀) are already desugared
 * into simply-typed lambda terms.
 *
 * It differs from the "real" lambda calculus in [[at.logic.gapt.expr]]
 * in three major ways:
 *
 *  1. There are type meta-variables.
 *  1. There are type annotations.
 *  1. Free variables, bound variables, and constants are not
 *     distinguished; they are all stored as "identifiers".
 */
object ast {

  class MetaTypeIdx {
    override def toString = Integer toHexString hashCode() take 3
  }
  def gensym() = new MetaTypeIdx

  sealed trait Type
  case class BaseType( name: String ) extends Type
  case class ArrType( a: Type, b: Type ) extends Type
  case class VarType( name: String ) extends Type
  case class MetaType( idx: MetaTypeIdx ) extends Type
  def freshMetaType() = MetaType( gensym() )

  sealed trait Expr
  case class TypeAnnotation( expr: Expr, ty: Type ) extends Expr
  case class Ident( name: String, ty: Type ) extends Expr
  case class Abs( v: Ident, sub: Expr ) extends Expr
  case class App( a: Expr, b: Expr ) extends Expr
  case class Lifted( e: real.LambdaExpression, ty: Type, fvs: Map[String, Type] ) extends Expr

  def readable( t: Type ): String = t match {
    case BaseType( name ) => name
    case VarType( name )  => s"?$name"
    case ArrType( a, b )  => s"(${readable( a )}>${readable( b )})"
    case MetaType( idx )  => s"_$idx"
  }
  def readable( e: Expr ): String = e match {
    case TypeAnnotation( expr, ty ) => s"(${readable( expr )}:${readable( ty )})"
    case Ident( name, ty )          => s"($name:${readable( ty )})"
    case Abs( v, sub )              => s"(^${readable( v )} ${readable( sub )})"
    case App( a, b )                => s"(${readable( a )} ${readable( b )})"
    case Lifted( e, ty, fvs )       => s"#lifted($e, ${readable( ty )}${fvs map { case ( n, t ) => s", $n -> ${readable( t )}" } mkString})"
  }

  def Bool = BaseType( "o" )

  def Eq( a: Expr, b: Expr ) = {
    val argType = freshMetaType()
    val eqType = ArrType( argType, ArrType( argType, Bool ) )
    App( App( Ident( real.EqC.name, eqType ), a ), b )
  }

  def Top = LiftBlackbox( real.Top() )
  def Bottom = LiftBlackbox( real.Bottom() )

  def UnaryConn( c: real.MonomorphicLogicalC ): Expr => Expr = a => App( LiftBlackbox( c() ), a )
  def Neg = UnaryConn( real.NegC )

  def BinaryConn( c: real.MonomorphicLogicalC ): ( Expr, Expr ) => Expr = ( a, b ) =>
    App( App( LiftBlackbox( c() ), a ), b )
  def And = BinaryConn( real.AndC )
  def Or = BinaryConn( real.OrC )
  def Bicond( a: Expr, b: Expr ) = And( Imp( a, b ), Imp( b, a ) )
  def Imp = BinaryConn( real.ImpC )

  def Quant( name: String ): ( Ident, Expr ) => Expr = ( v, sub ) =>
    App( Ident( name, ArrType( ArrType( freshMetaType(), Bool ), Bool ) ), Abs( v, sub ) )
  def Ex: ( Ident, Expr ) => Expr = Quant( real.ExistsC.name )
  def All = Quant( real.ForallC.name )

  def liftTypePoly( t: real.Ty ) = {
    val vars = mutable.Map[real.TVar, Type]()
    def lift( t: real.Ty ): Type = t match {
      case t: real.TVar         => vars.getOrElse( t, freshMetaType() )
      case real.TBase( name )   => BaseType( name )
      case real.`->`( in, out ) => ArrType( lift( in ), lift( out ) )
    }
    lift( t )
  }

  def liftTypeMono( t: real.Ty ): Type = t match {
    case real.TVar( name )    => VarType( name )
    case real.TBase( name )   => BaseType( name )
    case real.`->`( in, out ) => ArrType( liftTypeMono( in ), liftTypeMono( out ) )
  }

  def LiftBlackbox( e: real.LambdaExpression ) =
    Lifted( e, liftTypeMono( e.exptype ), Map() )

  def LiftWhitebox( e: real.LambdaExpression ) =
    Lifted( e, liftTypeMono( e.exptype ),
      real.freeVariables( e ).
      map { case real.Var( name, ty ) => name -> liftTypeMono( ty ) }.
      toMap )

  def freeMetas( t: Type ): Set[MetaTypeIdx] = t match {
    case BaseType( _ ) | VarType( _ ) => Set()
    case ArrType( a, b )              => freeMetas( a ) union freeMetas( b )
    case MetaType( idx )              => Set( idx )
  }

  def subst( t: Type, assg: Map[MetaTypeIdx, Type] ): Type = t match {
    case BaseType( _ ) | VarType( _ ) => t
    case ArrType( a, b )              => ArrType( subst( a, assg ), subst( b, assg ) )
    case MetaType( idx )              => assg.get( idx ).fold( t )( subst( _, assg ) )
  }
  type UnificationError = String
  def printCtx( eqs: List[( Type, Type )], assg: Map[MetaTypeIdx, Type] ): String =
    ( assg.map { case ( idx, t ) => s"${readable( MetaType( idx ) )} = ${readable( t )}\n" } ++
      eqs.map { case ( t1, t2 ) => s"${readable( t1 )} = ${readable( t2 )}\n" } ).mkString

  def solve( eqs: List[( Type, Type )], assg: Map[MetaTypeIdx, Type] ): UnificationError \/ Map[MetaTypeIdx, Type] = eqs match {
    case Nil => assg.right
    case ( first :: rest ) => first match {
      case ( ArrType( a1, b1 ), ArrType( a2, b2 ) ) =>
        solve( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, assg )
      case ( BaseType( n1 ), BaseType( n2 ) ) if n1 == n2 => solve( rest, assg )
      case ( VarType( n1 ), VarType( n2 ) ) if n1 == n2   => solve( rest, assg )
      case ( t1 @ MetaType( i1 ), t2 ) if assg contains i1 =>
        solve( ( assg( i1 ) -> t2 ) :: rest, assg )
      case ( t1 @ MetaType( i1 ), t2 ) =>
        val t2_ = subst( t2, assg )
        if ( t1 == t2_ )
          solve( rest, assg )
        else if ( freeMetas( t2_ ) contains i1 )
          s"Cannot unify types: ${readable( t1 )} occurs in ${readable( t2_ )} in\n${printCtx( eqs, assg )}".left
        else
          solve( rest, assg + ( i1 -> t2_ ) )
      case ( t1, t2: MetaType ) => solve( ( t2 -> t1 ) :: rest, assg )
      case ( t1, t2 )           => s"Cannot unify types ${readable( t1 )} and ${readable( t2 )} in\n${printCtx( eqs, assg )}".left
    }
  }

  def infers( exprs: Seq[Expr], env: Map[String, () => Type], s0: Map[MetaTypeIdx, Type] ): UnificationError \/ ( Map[MetaTypeIdx, Type], Seq[Type] ) =
    exprs match {
      case Seq() => ( s0 -> Seq() ).right
      case expr +: rest =>
        for {
          ( s1, exprt ) <- infer( expr, env, s0 )
          ( s2, restts ) <- infers( rest, env, s1 )
        } yield ( s2, exprt +: restts )
    }

  def infer( expr: Expr, env: Map[String, () => Type], s0: Map[MetaTypeIdx, Type] ): UnificationError \/ ( Map[MetaTypeIdx, Type], Type ) =
    expr match {
      case TypeAnnotation( e, t ) =>
        for {
          ( s1, et ) <- infer( e, env, s0 )
          s2 <- solve( List( et -> t ), s1 )
        } yield ( s2, et )
      case Ident( n, t ) =>
        if ( env contains n )
          for ( s1 <- solve( List( env( n )() -> t ), s0 ) ) yield ( s1, t )
        else ( s0 -> t ).right
      case Abs( Ident( vn, vt ), t ) =>
        for {
          ( s1, subt ) <- infer( t, env + ( vn -> ( () => vt ) ), s0 )
        } yield ( s1, ArrType( vt, subt ) )
      case App( a, b ) =>
        val appType = freshMetaType()
        for {
          ( s1, at ) <- infer( a, env, s0 )
          ( s2, bt ) <- infer( b, env, s1 )
          s3 <- solve( List( at -> ArrType( bt, appType ) ), s2 )
        } yield ( s3, appType )
      case Lifted( e, ty, fvs ) =>
        for {
          s1 <- solve( fvs.mapKeys( env( _ )() ).toList, s0 )
        } yield ( s1, ty )
    }

  def freeIdentifers( expr: Expr ): Set[String] = expr match {
    case TypeAnnotation( e, ty ) => freeIdentifers( e )
    case Ident( name, ty )       => Set( name )
    case Abs( v, sub )           => freeIdentifers( sub ) - v.name
    case App( a, b )             => freeIdentifers( a ) union freeIdentifers( b )
    case Lifted( e, ty, fvs )    => fvs.keySet
  }

  def toRealType( ty: Type, assg: Map[MetaTypeIdx, Type] ): real.Ty = ty match {
    case BaseType( name ) => real.TBase( name )
    case VarType( name )  => real.TVar( name )
    case ArrType( a, b )  => toRealType( a, assg ) -> toRealType( b, assg )
    case MetaType( idx )  => toRealType( assg( idx ), assg )
  }

  def toRealExpr( expr: Expr, assg: Map[MetaTypeIdx, Type], bound: Set[String] ): real.LambdaExpression = expr match {
    case TypeAnnotation( e, ty ) => toRealExpr( e, assg, bound )
    case expr @ Ident( name, ty ) =>
      if ( bound( name ) ) real.Var( name, toRealType( ty, assg ) )
      else real.Const( name, toRealType( ty, assg ) )
    case Abs( v @ Ident( vn, _ ), sub ) =>
      val bound_ = bound + vn
      real.Abs( toRealExpr( v, assg, bound_ ).asInstanceOf[real.Var], toRealExpr( sub, assg, bound_ ) )
    case App( a, b ) =>
      real.App( toRealExpr( a, assg, bound ), toRealExpr( b, assg, bound ) )
    case Lifted( e, ty, fvs ) => e
  }
  def toRealExprs( expr: Seq[Expr], sig: BabelSignature ): UnificationError \/ Seq[real.LambdaExpression] = {
    val fi = expr.view.flatMap( freeIdentifers ).toSet
    val freeVars = fi.filter( sig.signatureLookup( _ ).isVar )
    val startingEnv = fi.map { i =>
      i -> ( sig.signatureLookup( i ) match {
        case BabelSignature.IsConst( ty ) =>
          () => liftTypePoly( ty )
        case BabelSignature.IsUnknownConst | BabelSignature.IsVar =>
          val fixedMeta = freshMetaType()
          () => fixedMeta
      } )
    }
    for ( ( assg, _ ) <- infers( expr, startingEnv.toMap, Map() ) )
      yield expr.map( toRealExpr( _, assg.withDefaultValue( BaseType( "i" ) ), freeVars ) )
  }
  def toRealExpr( expr: Expr, sig: BabelSignature ): UnificationError \/ real.LambdaExpression =
    toRealExprs( Seq( expr ), sig ).map( _.head )
}
