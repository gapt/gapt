package gapt.expr

import cats.Monad
import cats.data.StateT
import cats.instances.either._
import cats.instances.list._
import cats.syntax.either._
import cats.syntax.traverse._
import gapt.expr
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.constants.NegC
import gapt.expr.formula.constants.OrC
import gapt.expr.ty.->:
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.freeVariables
import gapt.formats.babel.BabelSignature
import gapt.formats.babel.Notation
import gapt.utils.NameGenerator
import gapt.{ expr => real }

import scala.collection.mutable

/**
 * Intermediate representation for expressions without explicit types.
 *
 * The main application is during parsing: the [[gapt.formats.babel.BabelParser]]
 * produces pre-expressions.
 *
 * This representation is intended to be as simple as possible, all
 * higher-level constructs (such as <-> or ∀) are already desugared
 * into simply-typed lambda terms.
 *
 * It differs from the "real" lambda calculus in [[gapt.expr]]
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
  case class Ident( name: String, ty: Type, params: Option[List[Type]] ) extends Expr
  case class Abs( v: Ident, sub: Expr ) extends Expr
  case class App( a: Expr, b: Expr ) extends Expr
  case class Quoted( e: real.Expr, ty: Type, fvs: Map[String, Type] ) extends Expr
  type FlatOpsChild = Either[( String, Location ), Expr]
  case class FlatOps( children: List[FlatOpsChild] ) extends Expr

  class ReadablePrinter( assg: Map[MetaTypeIdx, Type], sig: BabelSignature ) {
    private val printMetaTypeIdx: MetaTypeIdx => String = {
      val names = LazyList.from( 1 ).map( i => s"_$i" ).iterator
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
      case LocAnnotation( expr, _ )      => apply( expr )
      case TypeAnnotation( expr, ty )    => s"(${apply( expr )}:${apply( ty )})"
      case Ident( name, ty, None )       => s"($name:${apply( ty )})"
      case Ident( name, ty, Some( ps ) ) => s"($name{${ps.map( apply ).mkString( " " )}:${apply( ty )})"
      case Abs( v, sub )                 => s"(^${apply( v )} ${apply( sub )})"
      case App( a, b )                   => s"(${apply( a )} ${apply( b )})"
      case Quoted( e, ty, fvs )          => s"#quote(${e.toSigRelativeString( sig )}, ${apply( ty )}${fvs map { case ( n, t ) => s", $n -> ${apply( t )}" } mkString})"
      case FlatOps( children )           => children.map { case Left( ( op, _ ) ) => op case Right( a ) => apply( a ) }.mkString( " " )
    }
  }

  def Bool = BaseType( "o", List() )

  def Eq( a: Expr, b: Expr ) = {
    val argType = freshMetaType()
    val eqType = ArrType( argType, ArrType( argType, Bool ) )
    App( App( Ident( EqC.name, eqType, Some( List( argType ) ) ), a ), b )
  }

  def Top = QuoteBlackbox( formula.Top() )
  def Bottom = QuoteBlackbox( formula.Bottom() )

  def UnaryConn( c: MonomorphicLogicalC ): Expr => Expr = a => App( QuoteBlackbox( c() ), a )
  def Neg = UnaryConn( NegC )

  def BinaryConn( c: MonomorphicLogicalC ): ( Expr, Expr ) => Expr = ( a, b ) =>
    App( App( QuoteBlackbox( c() ), a ), b )
  def And = BinaryConn( AndC )
  def Or = BinaryConn( OrC )
  def Iff( a: Expr, b: Expr ) = And( Imp( a, b ), Imp( b, a ) )
  def Imp = BinaryConn( ImpC )

  def Quant( name: String ): ( Ident, Expr ) => Expr = ( v, sub ) => {
    val quantTy = freshMetaType()
    App( Ident( name, ArrType( ArrType( quantTy, Bool ), Bool ), Some( List( quantTy ) ) ), Abs( v, sub ) )
  }
  def Ex = Quant( ExistsC.name )
  def All = Quant( ForallC.name )

  def liftTypePoly( t: Ty, ps: List[Ty] ) = {
    val vars = mutable.Map[TVar, Type]()
    def lift( t: Ty ): Type = t match {
      case t: TVar                       => vars.getOrElseUpdate( t, freshMetaType() )
      case real.ty.TBase( name, params ) => BaseType( name, params.map( lift ) )
      case ->:( in, out )                => ArrType( lift( in ), lift( out ) )
    }
    val res = ( lift( t ), ps.map( lift ) )
    res
  }

  def liftTypeMono( t: Ty ): Type = t match {
    case real.ty.TVar( name )          => VarType( name )
    case real.ty.TBase( name, params ) => BaseType( name, params.map( liftTypeMono ) )
    case ->:( in, out )                => ArrType( liftTypeMono( in ), liftTypeMono( out ) )
  }

  def QuoteBlackbox( e: real.Expr ) =
    Quoted( e, liftTypeMono( e.ty ), Map() )

  def QuoteWhitebox( e: real.Expr ) =
    Quoted( e, liftTypeMono( e.ty ),
      freeVariables( e ).
        map { case real.Var( name, ty ) => name -> liftTypeMono( ty ) }.
        toMap )

  def freeMetas( t: Type ): Set[MetaTypeIdx] = t match {
    case BaseType( _, params ) => params.view.flatMap( freeMetas ).toSet
    case VarType( _ )          => Set()
    case ArrType( a, b )       => freeMetas( a ) union freeMetas( b )
    case MetaType( idx )       => Set( idx )
  }
  def typeVars( t: Type ): Set[String] = t match {
    case BaseType( _, params ) => params.view.flatMap( typeVars ).toSet
    case VarType( n )          => Set( n )
    case ArrType( a, b )       => typeVars( a ) union typeVars( b )
    case MetaType( _ )         => Set()
  }

  def subst( t: Type, assg: Map[MetaTypeIdx, Type] ): Type = t match {
    case BaseType( n, ps ) => BaseType( n, ps.map( subst( _, assg ) ) )
    case VarType( _ )      => t
    case ArrType( a, b )   => ArrType( subst( a, assg ), subst( b, assg ) )
    case MetaType( idx )   => assg.get( idx ).fold( t )( subst( _, assg ) )
  }

  type Assg = Map[MetaTypeIdx, Type]
  sealed trait UnificationError { def assg: Assg }
  case class OccursCheck( t1: MetaType, t2: Type, assg: Assg ) extends UnificationError
  case class Mismatch( t1: Type, t2: Type, assg: Assg ) extends UnificationError

  def solve( eqs: List[( Type, Type )], assg: Map[MetaTypeIdx, Type] ): Either[UnificationError, Assg] = eqs match {
    case Nil => Right( assg )
    case ( first :: rest ) => first match {
      case ( ArrType( a1, b1 ), ArrType( a2, b2 ) ) =>
        solve( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, assg )
      case ( BaseType( n1, ps1 ), BaseType( n2, ps2 ) ) if n1 == n2 =>
        solve( ps1.lazyZip( ps2 ).toList ::: rest, assg )
      case ( VarType( n1 ), VarType( n2 ) ) if n1 == n2 => solve( rest, assg )
      case ( MetaType( i1 ), t2 ) if assg contains i1 =>
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

  def locsOf( exprs: Seq[Expr] ): Option[Location] =
    exprs.flatMap( locOf ) match {
      case locs if locs.nonEmpty =>
        Some( Location( locs.map( _.begin ).min, locs.map( _.end ).max ) )
      case _ => None
    }

  def locOf( expr: Expr ): Option[Location] =
    expr match {
      case LocAnnotation( _, loc ) => Some( loc )
      case TypeAnnotation( _, _ )  => None
      case Ident( _, _, _ )        => None
      case Abs( _, sub )           => locOf( sub )
      case App( a, b )             => locsOf( Seq( a, b ) )
      case Quoted( _, _, _ )       => None
      case FlatOps( children ) => locsOf( children.map {
        case Right( e )         => e
        case Left( ( _, loc ) ) => LocAnnotation( Top, loc )
      } )
    }

  type ElabState = Map[MetaTypeIdx, Type]
  case class ElabError( loc: Option[Location], msg: String, expected: Option[Type], actual: Option[Type], assg: ElabState )
  object ElabError {
    def apply( loc: Option[Location], msg: String, expected: Option[Type], actual: Type, assg: ElabState ): ElabError =
      ElabError( loc, msg, expected, Some( actual ), assg )
  }
  type ElabResult[X] = Either[ElabError, X]
  type Elab[X] = StateT[ElabResult, ElabState, X]

  type Env = Map[String, Type]

  def infers( exprs: Seq[Expr], env: Env )( implicit loc: Option[Location], sig: BabelSignature ): Elab[List[( Expr, Type )]] =
    exprs.toList.traverse( infer( _, env ) )

  def unify( a: Type, b: Type, mkErr: UnificationError => ElabError ): Elab[Unit] =
    StateT.modifyF[ElabResult, ElabState]( solve( List( a -> b ), _ ).leftMap( mkErr ) )

  def unifys( as: List[Type], bs: List[Type], mkErr: UnificationError => ElabError ): Elab[Unit] =
    if ( as.size != bs.size ) StateT.inspectF( assg_ => Left( mkErr( new UnificationError { override def assg: Assg = assg_ } ) ) ) else
      ( as zip bs ).traverse { case ( a, b ) => unify( a, b, mkErr ) }.map( _ => () )

  def infer( expr: Expr, env: Env )( implicit loc: Option[Location], sig: BabelSignature ): Elab[( Expr, Type )] =
    expr match {
      case LocAnnotation( e, loc_ ) =>
        infer( e, env )( Some( loc_ ), sig )
      case TypeAnnotation( e, t ) =>
        for {
          ei <- infer( e, env ); ( _, et ) = ei
          _ <- unify( et, t, err => ElabError( loc, s"mismatched annotated type", Some( t ), et, err.assg ) )
        } yield ei
      case Ident( n, t, ps ) =>
        if ( ps.isEmpty && env.contains( n ) ) {
          val tyInEnv = env( n )
          for {
            _ <- unify( tyInEnv, t, err => ElabError( loc, "mismatched identifier type", Some( t ), tyInEnv, err.assg ) )
          } yield ( Ident( n, t, None ), t )
        } else sig.signatureLookup( n ) match {
          case BabelSignature.IsConst( c ) =>
            val ( tyInSig, params ) = liftTypePoly( c.ty, c.params )
            for {
              _ <- unifys( ps.getOrElse( params ), params, err => ElabError(
                loc,
                s"mismatched constant type parameters: expected ${params.size}, actual ${ps.size}",
                Some( t ), tyInSig, err.assg ) )
              _ <- unify( tyInSig, t, err => ElabError( loc, "mismatched identifier type", Some( t ), tyInSig, err.assg ) )
            } yield ( Ident( n, t, Some( params ) ), t )
          case BabelSignature.IsUnknownConst | BabelSignature.IsVar =>
            Monad[Elab].pure( ( Ident( n, t, ps ), t ) )
        }
      case Abs( v @ Ident( vn, vt, _ ), t ) =>
        for {
          ti <- infer( t, env + ( vn -> vt ) ); ( sube, subt ) = ti
        } yield ( Abs( v, sube ), ArrType( vt, subt ): Type )
      case App( a, b ) =>
        val resType = freshMetaType()
        val argType = freshMetaType()
        for {
          ai <- infer( a, env ); ( a_, at ) = ai
          _ <- unify( at, ArrType( argType, resType ), err => ElabError( locOf( a ).orElse( loc ), "not a function", None, at, err.assg ) )
          bi <- infer( b, env ); ( b_, bt ) = bi
          _ <- unify( bt, argType, err => ElabError(
            locOf( b ).orElse( loc ),
            s"incorrect type for argument", Some( argType ), bt, err.assg ) )
        } yield ( App( a_, b_ ), resType: Type )
      case Quoted( e, ty, fvs ) =>
        fvs.toList.traverse {
          case ( name, fvTy ) =>
            val tyInEnv = env( name ) // params don't matter since we only look at free vars
            unify( tyInEnv, fvTy, err =>
              ElabError( loc, s"mismatched type for free variable $name in quote $e", Some( tyInEnv ), fvTy, err.assg ) )
        }.map( _ => ( expr, ty ) )
      case FlatOps( children ) =>
        for {
          deflattened <- parseFlatOpFirst( children, env, minPrec = 0 )
          _ = require( deflattened._2.isEmpty )
          inferred <- infer( deflattened._1, env )
        } yield inferred
    }

  def elabError[T]( msg: String, atExpr: Expr )( implicit loc: Option[Location] ): Elab[T] =
    elabError( msg )( locOf( atExpr ).orElse( loc ) )

  def elabError[T]( msg: String )( implicit loc: Option[Location] ): Elab[T] =
    StateT.apply[ElabResult, ElabState, T]( assg => Left( ElabError( loc, msg, None, None, assg ) ) )

  def elabIdent( e: Expr )( implicit loc: Option[Location] ): Elab[Ident] =
    e match {
      case LocAnnotation( e2, loc_ ) => elabIdent( e2 )( Some( loc_ ) )
      case TypeAnnotation( e2, ty ) =>
        for {
          res <- elabIdent( e2 )
          _ <- unify( res.ty, ty, err => ElabError( loc, s"mismatched annotated type", Some( ty ), res.ty, err.assg ) )
        } yield res
      case vn @ Ident( _, _, _ ) => Monad[Elab].pure( vn )
      case FlatOps( List( ch ) ) => elabIdent( ch )
      case Quoted( Var( vNew, _ ), ty, _ ) =>
        Monad[Elab].pure( Ident( vNew, ty, None ) )
      case _ =>
        elabError( "not an identifier", e )
    }
  def elabIdent( ch: FlatOpsChild )( implicit loc: Option[Location] ): Elab[Ident] =
    ch match {
      case Left( ( n, _ ) ) => Monad[Elab].pure( Ident( n, freshMetaType(), None ) )
      case Right( e )       => elabIdent( e )
    }

  def parseFlatOpFirst( flatOpsChildren: List[FlatOpsChild], env: Env, minPrec: Int )( implicit loc: Option[Location], sig: BabelSignature ): Elab[( Expr, List[FlatOpsChild] )] =
    flatOpsChildren match {
      case Nil => elabError( "empty expression" )
      case ( Left( ( n, idLoc ) ) :: children_ ) =>
        val expr = LocAnnotation( Ident( n, freshMetaType(), None ), idLoc )
        sig.notationsForToken( Notation.Token( n ) ) match {
          case Some( not ) if not.precedence < minPrec => elabError( "missing expression before", expr )
          case Some( not ) if not.precedence >= minPrec =>
            val fn = not.const match {
              case Notation.RealConst( c ) =>
                Some( LocAnnotation( Ident( c, freshMetaType(), None ), idLoc ) )
              case _ => None
            }
            not match {
              case _ if children_.isEmpty => Monad[Elab].pure( fn.get -> Nil )
              case Notation.Alias( _, _ ) =>
                parseFlatOpRest( children_, fn.get, env, minPrec )
              case Notation.Prefix( _, _, prec ) =>
                if ( children_.isEmpty ) Monad[Elab].pure( fn.get -> Nil ) else for {
                  res <- parseFlatOpFirst( children_, env, math.max( prec, minPrec ) )
                  ( arg, children__ ) = res
                  res2 <- parseFlatOpRest( children__, App( fn.get, arg ), env, minPrec )
                } yield res2
              case Notation.Quantifier( _, _, prec ) =>
                for {
                  v <- elabIdent( children_.head )
                  env1 = env + ( v.name -> v.ty )
                  res <- parseFlatOpFirst( children_.tail, env1, math.max( prec, minPrec ) )
                  ( body, children__ ) = res
                  res2 <- parseFlatOpRest( children__, App( fn.get, Abs( v, body ) ), env, minPrec )
                } yield res2
              case _ if fn.isEmpty =>
                elabError( s"${not.token} needs argument on the left", expr )
              case _ =>
                for {
                  res <- parseFlatOpFirst( children_, env, not.precedence )
                  ( arg, children__ ) = res
                  res2 <- parseFlatOpRest( children__, App( fn.get, arg ), env, minPrec )
                } yield res2
            }
          case None =>
            parseFlatOpRest( children_, expr, env, minPrec )
        }
      case Right( expr ) :: children_ =>
        parseFlatOpRest( children_, expr, env, minPrec )
    }

  def mkBinOp( c: Notation.ConstName, fn: Option[Expr], arg1: Expr, arg2: Expr ): Expr =
    c match {
      case Notation.fakeIffConst => Iff( arg1, arg2 )
      case Notation.fakeNeqConst => Neg( Eq( arg1, arg2 ) )
      case _                     => App( App( fn.get, arg1 ), arg2 )
    }

  def parseFlatOpRest( flatOpsChildren: List[FlatOpsChild], lhsExpr: Expr, env: Env, minPrec: Int )( implicit loc: Option[Location], sig: BabelSignature ): Elab[( Expr, List[FlatOpsChild] )] =
    flatOpsChildren match {
      case Nil => Monad[Elab].pure( lhsExpr -> Nil )
      case ( Left( ( n, idLoc ) ) :: children_ ) =>
        val expr = LocAnnotation( Ident( n, freshMetaType(), None ), idLoc )
        sig.notationsForToken( Notation.Token( n ) ) match {
          case Some( not ) if not.precedence < minPrec =>
            Monad[Elab].pure( lhsExpr -> flatOpsChildren )
          case Some( not ) if not.precedence >= minPrec =>
            val fn = not.const match {
              case Notation.RealConst( c ) =>
                Some( LocAnnotation( Ident( c, freshMetaType(), None ), idLoc ) )
              case _ => None
            }
            not match {
              case Notation.Infix( _, _, prec, leftAssoc ) =>
                if ( children_.nonEmpty )
                  for {
                    res <- parseFlatOpFirst( children_, env, math.max( minPrec, if ( leftAssoc ) prec + 1 else prec ) )
                    ( arg2, children__ ) = res
                    res2 <- parseFlatOpRest( children__, mkBinOp( not.const, fn, lhsExpr, arg2 ), env, minPrec )
                  } yield res2
                else if ( Notation.isFakeConst( not.const ) )
                  elabError( s"${not.token} needs argument on the right", expr )
                else
                  Monad[Elab].pure( App( fn.get, lhsExpr ) -> Nil )
              case Notation.Prefix( _, _, prec ) =>
                for {
                  res <- parseFlatOpFirst( children_, env, prec )
                  ( arg, children__ ) = res
                  res2 <- parseFlatOpRest( children__, App( lhsExpr, App( fn.get, arg ) ), env, minPrec )
                } yield res2
              case Notation.Postfix( _, _, _ ) =>
                parseFlatOpRest( children_, App( fn.get, lhsExpr ), env, minPrec )
              case Notation.Alias( _, _ ) =>
                parseFlatOpRest( children_, App( lhsExpr, fn.get ), env, minPrec )
              case _ =>
                for {
                  res <- parseFlatOpFirst( flatOpsChildren, env, minPrec )
                  ( arg, children__ ) = res
                  res2 <- parseFlatOpRest( children__, App( lhsExpr, arg ), env, minPrec )
                } yield res2
            }
          case None =>
            parseFlatOpRest( children_, App( lhsExpr, expr ), env, minPrec )
        }
      case ( Right( expr ) :: children_ ) =>
        parseFlatOpRest( children_, App( lhsExpr, expr ), env, minPrec )
    }

  def freeIdentifers( expr: Expr ): Set[String] = expr match {
    case LocAnnotation( e, _ )  => freeIdentifers( e )
    case TypeAnnotation( e, _ ) => freeIdentifers( e )
    case Ident( name, _, _ )    => Set( name )
    case Abs( v, sub )          => freeIdentifers( sub ) - v.name
    case App( a, b )            => freeIdentifers( a ) union freeIdentifers( b )
    case Quoted( _, _, fvs )    => fvs.keySet
    case FlatOps( children ) => children.view.flatMap {
      case Left( ( id, _ ) ) => Set( id )
      case Right( ex )       => freeIdentifers( ex )
    }.toSet
  }

  def types( expr: Expr ): Set[Type] = expr match {
    case LocAnnotation( e, _ )  => types( e )
    case TypeAnnotation( e, _ ) => types( e )
    case Ident( _, ty, ps )     => Set( ty ) ++ ps.getOrElse( Nil )
    case Abs( v, sub )          => types( v ) ++ types( sub )
    case App( a, b )            => types( a ) ++ types( b )
    case Quoted( _, _, fvs )    => fvs.values.toSet
    case FlatOps( children ) => children.view.flatMap {
      case Left( _ )   => Set[Type]()
      case Right( ch ) => types( ch )
    }.toSet
  }

  def toRealType( ty: Type, assg: Map[MetaTypeIdx, Type] ): Ty = ty match {
    case BaseType( name, params ) => TBase( name, params.map( toRealType( _, assg ) ) )
    case VarType( name )          => expr.ty.TVar( name )
    case ArrType( a, b )          => toRealType( a, assg ) ->: toRealType( b, assg )
    case MetaType( idx )          => toRealType( assg( idx ), assg )
  }

  def toRealExpr( expr: Expr, assg: Map[MetaTypeIdx, Type], bound: Set[String] ): real.Expr = expr match {
    case LocAnnotation( e, _ )  => toRealExpr( e, assg, bound )
    case TypeAnnotation( e, _ ) => toRealExpr( e, assg, bound )
    case Ident( name, ty, None ) =>
      if ( bound( name ) ) real.Var( name, toRealType( ty, assg ) )
      else real.Const( name, toRealType( ty, assg ) )
    case Ident( name, ty, Some( ps ) ) =>
      real.Const( name, toRealType( ty, assg ), ps.map( toRealType( _, assg ) ) )
    case Abs( v @ Ident( vn, _, _ ), sub ) =>
      val bound_ = bound + vn
      real.Abs( toRealExpr( v, assg, bound_ ).asInstanceOf[real.Var], toRealExpr( sub, assg, bound_ ) )
    case App( a, b ) =>
      real.App( toRealExpr( a, assg, bound ), toRealExpr( b, assg, bound ) )
    case Quoted( e, _, _ ) => e
    case FlatOps( _ ) =>
      throw new IllegalArgumentException( expr.toString )
  }
  def toRealExprs( expr: Seq[Expr], sig: BabelSignature ): Either[ElabError, Seq[real.Expr]] = {
    val fi = expr.view.flatMap( freeIdentifers ).toSet
    val freeVars = fi.filter( sig.signatureLookup( _ ).isVar )
    val startingEnv: Env = Map() ++ fi.flatMap { i =>
      sig.signatureLookup( i ) match {
        case BabelSignature.IsConst( _ ) => None
        case BabelSignature.IsUnknownConst | BabelSignature.IsVar =>
          Some( i -> freshMetaType() )
      }
    }
    infers( expr, startingEnv )( None, sig ).run( Map() ).map {
      case ( assg, expr_ ) =>
        val exprs = expr_.map( _._1 )
        val nameGen = new NameGenerator( ( exprs.view.flatMap( types ) ++ assg.values ).flatMap( typeVars ) )
        val cache = mutable.Map[MetaTypeIdx, Type]()
        val assg_ = assg.withDefault( m => cache.getOrElseUpdate(
          m,
          if ( sig.defaultTypeToI ) BaseType( "i", Nil ) else VarType( nameGen.fresh( "a" ) ) ) )
        exprs.map( toRealExpr( _, assg_, freeVars ) )
    }
  }
  def toRealExpr( expr: Expr, sig: BabelSignature ): Either[ElabError, real.Expr] =
    toRealExprs( Seq( expr ), sig ).map( _.head )
}
