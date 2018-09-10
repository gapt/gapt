package extraction

import gapt.expr._
import gapt.proofs.Context

object FSharpCodeGenerator extends CodeGenerator {

  def generateBoilerPlate( e: Expr )( implicit context: Context ): String = {
    def typeParamToString( param: Ty ) = "'" + param.toString.substring( 1 ).toLowerCase()

    var definedSumType = false

    val prefix =
      """
        |open System
        |
        |""".stripMargin

    val definitions =
      context.constants.filter {
        case Const( "i", _, _ )
          | Const( "0", _, _ ) => false
        case _ => true
      }.map {
        // TODO: b = (a => exn)
        /*
        case Const( "bar", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          val c = typeParamToString( params( 2 ) )
          s"let bar (p2: $a -> $c) (p3: $b -> $c): $c = raise (NotImplementedException())"
        case Const( "bar2", _, params ) =>
          val p = typeParamToString( params( 0 ) )
          val a = typeParamToString( params( 1 ) )
          val b = typeParamToString( params( 2 ) )
          val c = typeParamToString( params( 3 ) )
          s"let bar2 (p1: $p -> bool) (p2: $a -> $c) (p3: $b -> $c): $c = raise (NotImplementedException())"
          */
        case Const( "pair", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          s"let pair (p0: $a)(p1: $b) = (p0, p1)"
        case Const( "pi1", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          s"let pi1 (p: $a*$b) = fst p"
        case Const( "pi2", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          s"let pi2 (p: $a*$b) = snd p"
        case Const( "inl", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          val res = ( if ( !definedSumType ) s"type Sum<$a,$b> = Inl of $a | Inr of $b\n" else "" ) +
            s"let inl<$a,$b> ( v: $a ): Sum<$a,$b> = Inl v"
          definedSumType = true
          res
        case Const( "inr", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          val res = ( if ( !definedSumType ) s"type Sum<$a,$b> = Inl of $a | Inr of $b\n" else "" ) +
            s"let inr<$a,$b> ( v: $b ): Sum<$a,$b> = Inr v"

          definedSumType = true
          res
        case Const( "matchSum", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          val b = typeParamToString( params( 1 ) )
          val c = typeParamToString( params( 2 ) )
          val res = ( if ( !definedSumType ) s"type Sum<$a,$b> = Inl of $a | Inr of $b\n" else "" ) +
            s"""
let matchSum (p1: Sum<$a,$b>) (p2: $a -> $c) (p3: $b -> $c) =
  match p1 with
  | Inl a -> p2 a
  | Inr b -> p3 b
"""
          definedSumType = true
          res
        case Const( "s", _, params ) =>
          s"let s (x: int) = x + 1"
        case Const( "efq", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          s"let efq<$a> (p: exn): $a = raise p"
        // TODO: FSharp does not support type parameters with exceptions, need to generate one for each type
        case Const( "exception", _, params ) =>
          s"""
type T = INT of int | UNIT | PAIR of T * T
let rec wrap (v: 'a) =
  match v with
  | (i : int) -> INT i
  | :? unit -> UNIT
  | (v1, v2) -> PAIR (wrap v1, wrap v2)
let rec unwrap (v: T): 'a =
  match v with
  | INT i -> i
  | UNIT -> ()
  | PAIR (v1, v2) -> unwrap v1, unwrap v2
exception NewException of T
let newException (p: T) = (NewException p)"""
        case Const( "pow2", _, params ) =>
          s"let pow2 (x: int) = x * x"
        case Const( "*", _, params ) =>
          s"let mul (x: int) (y: int) = x * y"
        case Const( "<=", _, params ) =>
          s"let leq (x: int) (y: int) = x <= y"
        case Const( "<", _, params ) =>
          s"let lt (x: int) (y: int) = x < y"
        case Const( "=", _, params ) =>
          val x = typeParamToString( params( 0 ) )
          s"let eq (x: $x) (y: $x) = (x = y)"
        case Const( "natRec", _, params ) =>
          val a = typeParamToString( params( 0 ) )
          s"""
let rec natRec (p1: $a) (p2: (int -> $a -> $a)) (p3: int): $a =
  if(p3 = 0) then p1
  else p2 (p3-1) (natRec (p1) (p2) (p3-1) )
"""
        case c @ _ =>
          ""
        //"not yet implemented: " + c.toString
      }.mkString( "\n" )
    prefix + definitions
  }

  def toTerm( c: Const ): String = {
    c match {
      //case Const( "i", _, _ )  => "null"
      case Const( "i", _, _ )  => "()"
      case Const( "*", _, _ )  => "mul"
      case Const( "<=", _, _ ) => "leq"
      case Const( "<", _, _ )  => "lt"
      case Const( "=", _, _ )  => "eq"
      case Const( "inl", _, params ) =>
        s"inl<${params.map( toType( _ ) ).mkString( "," )}>"
      case Const( "inr", _, params ) =>
        s"inr<${params.map( toType( _ ) ).mkString( "," )}>"
      case Const( "efq", _, params ) =>
        s"efq<${params.map( toType( _ ) ).mkString( "," )}>"
      case _ => c.name
    }
  }

  def toType( t: Ty ): String = {
    t match {
      //case TBase( "1", Nil ) => "Null"
      case TBase( "1", Nil ) => "unit"
      case TBase( "nat", Nil )
        | TBase( "i", Nil ) => "int"
      case TBase( "o", Nil )       => "bool"
      case TBase( "exn", Nil )     => "exn"
      case TBase( "conj", params ) => s"(${toType( params( 0 ) )}*${toType( params( 1 ) )})"
      case TBase( "sum", params )  => s"Sum<${toType( params( 0 ) )}, ${toType( params( 1 ) )}>"
      case TArr( t1, t2 )          => s"(${toType( t1 )} -> ${toType( t2 )})"
      case _                       => t.toString
    }
  }

  var bugIdentifier = 0
  def translate( e: Expr )( implicit ctx: Context ): String = {
    e match {
      case App( App( Const( "em", _, params ), catchTerm ), tryTerm ) =>
        bugIdentifier = bugIdentifier + 1
        s"""
(
try
  ( ${translate( tryTerm )} ( wrap >> newException ) )
with
  | NewException( exceptionValue ) -> ( ${translate( catchTerm )} ( unwrap exceptionValue ) )
  | e -> printfn "BUG $bugIdentifier" ; raise e
) """
      case App( e1, e2 ) =>
        s"(${translate( e1 )} ${translate( e2 )})"
      case Abs( v, e ) =>
        s"(fun (${v.name} : ${toType( v.ty )}) -> ${translate( e )})"
      case Var( name, _ ) =>
        name
      case c: Const =>
        toTerm( c )
    }
  }
}
