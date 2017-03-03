package at.logic.gapt.expr

import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.{ expr => real }
import cats.Monad
import cats.data.StateT
import cats.syntax.traverse._
import cats.syntax.either._
import cats.instances.list._
import cats.instances.either._

import scala.collection.mutable

/**
 * Intermediate representation for expressions without explicit types.
 *
 * The main application is during parsing: the [[at.logic.gapt.formats.babel.BabelParser]]
 * produces pre-expressions.
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
object preExpr {

  class MetaTypeIdx {
    override def toString = Integer toHexString hashCode() take 3
  }

  sealed trait Type
  case class BaseType( name: String, params: List[Type] ) extends Type
  case class ArrType( a: Type, b: Type ) extends Type
  case class VarType( name: String ) extends Type
  case class MetaType( idx: MetaTypeIdx ) extends Type
  def freshMetaType() = MetaType( new MetaTypeIdx )

  case class Location( begin: Int, end: Int )

  sealed trait Expr
  case class LocAnnotation( expr: Expr, loc: Location ) extends Expr
  case class TypeAnnotation( expr: Expr, ty: Type ) extends Expr
  case class Ident( name: String, ty: Type ) extends Expr
  case class Abs( v: Ident, sub: Expr ) extends Expr
  case class App( a: Expr, b: Expr ) extends Expr
  case class Quoted( e: real.LambdaExpression, ty: Type, fvs: Map[String, Type] ) extends Expr

  class ReadablePrinter( assg: Map[MetaTypeIdx, Type], sig: BabelSignature ) {
    private val printMetaTypeIdx: MetaTypeIdx => String = {
      val names = Stream.from( 1 ).map( i => s"_$i" ).iterator
      val cache = mutable.Map[MetaTypeIdx, String]()
      idx => cache.getOrElseUpdate( idx, names.next() )
    }

    def apply( t: Type ): String = t match {
      case BaseType( name, params ) => s"$name${params.map( x => " " + apply( x ) ).mkString}"
      case VarType( name )          => s"?$name"
      case ArrType( a, b )          => s"(${apply( a )}>${apply( b )})"
      case MetaType( idx ) =>
        assg.get( idx ).map( apply ).getOrElse( printMetaTypeIdx( idx ) )
    }
    def apply( e: Expr ): String = e match {
      case LocAnnotation( expr, _ )   => apply( expr )
      case TypeAnnotation( expr, ty ) => s"(${apply( expr )}:${apply( ty )})"
      case Ident( name, ty )          => s"($name:${apply( ty )})"
      case Abs( v, sub )              => s"(^${apply( v )} ${apply( sub )})"
      case App( a, b )                => s"(${apply( a )} ${apply( b )})"
      case Quoted( e, ty, fvs )       => s"#quote(${e.toSigRelativeString( sig )}, ${apply( ty )}${fvs map { case ( n, t ) => s", $n -> ${apply( t )}" } mkString})"
    }
  }

  def Bool = BaseType( "o", List() )

  def Eq( a: Expr, b: Expr ) = {
    val argType = freshMetaType()
    val eqType = ArrType( argType, ArrType( argType, Bool ) )
    App( App( Ident( real.EqC.name, eqType ), a ), b )
  }

  def Top = QuoteBlackbox( real.Top() )
  def Bottom = QuoteBlackbox( real.Bottom() )

  def UnaryConn( c: real.MonomorphicLogicalC ): Expr => Expr = a => App( QuoteBlackbox( c() ), a )
  def Neg = UnaryConn( real.NegC )

  def BinaryConn( c: real.MonomorphicLogicalC ): ( Expr, Expr ) => Expr = ( a, b ) =>
    App( App( QuoteBlackbox( c() ), a ), b )
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
      case t: real.TVar               => vars.getOrElseUpdate( t, freshMetaType() )
      case real.TBase( name, params ) => BaseType( name, params.map( lift ) )
      case real.`->`( in, out )       => ArrType( lift( in ), lift( out ) )
    }
    lift( t )
  }

  def liftTypeMono( t: real.Ty ): Type = t match {
    case real.TVar( name )          => VarType( name )
    case real.TBase( name, params ) => BaseType( name, params.map( liftTypeMono ) )
    case real.`->`( in, out )       => ArrType( liftTypeMono( in ), liftTypeMono( out ) )
  }

  def QuoteBlackbox( e: real.LambdaExpression ) =
    Quoted( e, liftTypeMono( e.exptype ), Map() )

  def QuoteWhitebox( e: real.LambdaExpression ) =
    Quoted( e, liftTypeMono( e.exptype ),
      real.freeVariables( e ).
      map { case real.Var( name, ty ) => name -> liftTypeMono( ty ) }.
      toMap )

  def freeMetas( t: Type ): Set[MetaTypeIdx] = t match {
    case BaseType( _, params ) => params.view.flatMap( freeMetas ).toSet
    case VarType( _ )          => Set()
    case ArrType( a, b )       => freeMetas( a ) union freeMetas( b )
    case MetaType( idx )       => Set( idx )
  }

  def subst( t: Type, assg: Map[MetaTypeIdx, Type] ): Type = t match {
    case BaseType( n, ps ) => BaseType( n, ps.map( subst( _, assg ) ) )
    case VarType( _ )      => t
    case ArrType( a, b )   => ArrType( subst( a, assg ), subst( b, assg ) )
    case MetaType( idx )   => assg.get( idx ).fold( t )( subst( _, assg ) )
  }
  trait UnificationError {
    def assg: Map[MetaTypeIdx, Type]
  }
  case class OccursCheck( t1: MetaType, t2: Type, assg: Map[MetaTypeIdx, Type] ) extends UnificationError
  case class Mismatch( t1: Type, t2: Type, assg: Map[MetaTypeIdx, Type] ) extends UnificationError

  def solve( eqs: List[( Type, Type )], assg: Map[MetaTypeIdx, Type] ): Either[UnificationError, Map[MetaTypeIdx, Type]] = eqs match {
    case Nil => Right( assg )
    case ( first :: rest ) => first match {
      case ( ArrType( a1, b1 ), ArrType( a2, b2 ) ) =>
        solve( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, assg )
      case ( BaseType( n1, ps1 ), BaseType( n2, ps2 ) ) if n1 == n2 =>
        solve( ( ps1, ps2 ).zipped.toList ::: rest, assg )
      case ( VarType( n1 ), VarType( n2 ) ) if n1 == n2 => solve( rest, assg )
      case ( t1 @ MetaType( i1 ), t2 ) if assg contains i1 =>
        solve( ( assg( i1 ) -> t2 ) :: rest, assg )
      case ( t1 @ MetaType( i1 ), t2 ) =>
        val t2_ = subst( t2, assg )
        if ( t1 == t2_ )
          solve( rest, assg )
        else if ( freeMetas( t2_ ) contains i1 )
          Left( OccursCheck( t1, t2_, assg ) )
        else
          solve( rest, assg + ( i1 -> t2_ ) )
      case ( t1, t2: MetaType ) => solve( ( t2 -> t1 ) :: rest, assg )
      case ( t1, t2 )           => Left( Mismatch( t1, t2, assg ) )
    }
  }

  def locOf( expr: Expr ): Option[Location] =
    expr match {
      case LocAnnotation( _, loc ) => Some( loc )
      case TypeAnnotation( _, _ )  => None
      case Ident( _, _ )           => None
      case Abs( _, sub )           => locOf( sub )
      case App( a, b ) =>
        ( locOf( a ), locOf( b ) ) match {
          case ( None, None )                 => None
          case ( Some( loc ), None )          => Some( loc )
          case ( None, Some( loc ) )          => Some( loc )
          case ( Some( loc1 ), Some( loc2 ) ) => Some( Location( math.min( loc1.begin, loc2.begin ), math.max( loc2.end, loc2.end ) ) )
        }
      case Quoted( _, _, _ ) => None
    }

  type ElabState = Map[MetaTypeIdx, Type]
  case class ElabError( loc: Option[Location], msg: String, expected: Option[Type], actual: Type, assg: ElabState )
  type ElabResult[X] = Either[ElabError, X]
  type Elab[X] = StateT[ElabResult, ElabState, X]

  def infers( exprs: Seq[Expr], env: Map[String, () => Type] )( implicit loc: Option[Location] ): Elab[List[Type]] =
    exprs.toList.traverse( infer( _, env ) )

  def unify( a: Type, b: Type, mkErr: UnificationError => ElabError ): Elab[Unit] =
    StateT.modifyF[ElabResult, ElabState]( solve( List( a -> b ), _ ).leftMap( mkErr ) )

  def infer( expr: Expr, env: Map[String, () => Type] )( implicit loc: Option[Location] ): Elab[Type] =
    expr match {
      case LocAnnotation( e, loc_ ) =>
        infer( e, env )( Some( loc_ ) )
      case TypeAnnotation( e, t ) =>
        for {
          et <- infer( e, env )
          _ <- unify( et, t, err => ElabError( loc, s"mismatched annotated type", Some( t ), et, err.assg ) )
        } yield et
      case Ident( n, t ) =>
        if ( env contains n ) {
          val tyInEnv = env( n )()
          for {
            _ <- unify( tyInEnv, t, err => ElabError( loc, "mismatched identifier type", Some( t ), tyInEnv, err.assg ) )
          } yield t
        } else Monad[Elab].pure( t )
      case Abs( Ident( vn, vt ), t ) =>
        for {
          subt <- infer( t, env + ( vn -> ( () => vt ) ) )
        } yield ArrType( vt, subt ): Type
      case App( a, b ) =>
        val resType = freshMetaType()
        val argType = freshMetaType()
        for {
          at <- infer( a, env )
          _ <- unify( at, ArrType( argType, resType ), err => ElabError( locOf( a ).orElse( loc ), "not a function", None, at, err.assg ) )
          bt <- infer( b, env )
          _ <- unify( bt, argType, err => ElabError( locOf( b ).orElse( loc ), "incorrect type for argument", Some( argType ), bt, err.assg ) )
        } yield resType: Type
      case Quoted( e, ty, fvs ) =>
        fvs.toList.traverse {
          case ( name, fvTy ) =>
            val tyInEnv = env( name )()
            unify( tyInEnv, fvTy, err =>
              ElabError( loc, s"mismatched type for free variable $name in quote $e", Some( tyInEnv ), fvTy, err.assg ) )
        }.map( _ => ty )
    }

  def freeIdentifers( expr: Expr ): Set[String] = expr match {
    case LocAnnotation( e, _ )   => freeIdentifers( e )
    case TypeAnnotation( e, ty ) => freeIdentifers( e )
    case Ident( name, ty )       => Set( name )
    case Abs( v, sub )           => freeIdentifers( sub ) - v.name
    case App( a, b )             => freeIdentifers( a ) union freeIdentifers( b )
    case Quoted( e, ty, fvs )    => fvs.keySet
  }

  def toRealType( ty: Type, assg: Map[MetaTypeIdx, Type] ): real.Ty = ty match {
    case BaseType( name, params ) => real.TBase( name, params.map( toRealType( _, assg ) ) )
    case VarType( name )          => real.TVar( name )
    case ArrType( a, b )          => toRealType( a, assg ) -> toRealType( b, assg )
    case MetaType( idx )          => toRealType( assg( idx ), assg )
  }

  def toRealExpr( expr: Expr, assg: Map[MetaTypeIdx, Type], bound: Set[String] ): real.LambdaExpression = expr match {
    case LocAnnotation( e, _ )   => toRealExpr( e, assg, bound )
    case TypeAnnotation( e, ty ) => toRealExpr( e, assg, bound )
    case Ident( name, ty ) =>
      if ( bound( name ) ) real.Var( name, toRealType( ty, assg ) )
      else real.Const( name, toRealType( ty, assg ) )
    case Abs( v @ Ident( vn, _ ), sub ) =>
      val bound_ = bound + vn
      real.Abs( toRealExpr( v, assg, bound_ ).asInstanceOf[real.Var], toRealExpr( sub, assg, bound_ ) )
    case App( a, b ) =>
      real.App( toRealExpr( a, assg, bound ), toRealExpr( b, assg, bound ) )
    case Quoted( e, _, _ ) => e
  }
  def toRealExprs( expr: Seq[Expr], sig: BabelSignature ): Either[ElabError, Seq[real.LambdaExpression]] = {
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
    infers( expr, startingEnv.toMap )( None ).run( Map() ).map {
      case ( assg, _ ) =>
        expr.map( toRealExpr( _, assg.withDefaultValue( BaseType( "i", Nil ) ), freeVars ) )
    }
  }
  def toRealExpr( expr: Expr, sig: BabelSignature ): Either[ElabError, real.LambdaExpression] =
    toRealExprs( Seq( expr ), sig ).map( _.head )
}
