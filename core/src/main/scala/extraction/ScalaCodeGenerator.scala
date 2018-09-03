package extraction

import gapt.expr._
import gapt.proofs.Context

object ScalaCodeGenerator extends CodeGenerator {

  def generateBoilerPlate( implicit context: Context ): String = {
    def typeParamToString( param: Ty ) = param.toString.substring( 1 ).toUpperCase()

    var definedSumType = false

    val prefix =
      """
        |object extracted extends App {
        |""".stripMargin

    val suffix =
      """
        |}
        |""".stripMargin

    val definitions = context.constants.filter {
      case Const( "i", _, _ )
        | Const( "0", _, _ ) => false
      case _ => true
    }.map {
      // TODO: b = (a => exn)
      case Const( "bar", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val c = typeParamToString( params( 2 ) )
        s"def bar[$a,$b,$c](p2: $a => $c)(p3: $b => $c): $c = {???}"
      /*
      case Const( "bar2", _, params ) =>
        val p = typeParamToString( params( 0 ) )
        val a = typeParamToString( params( 1 ) )
        val b = typeParamToString( params( 2 ) )
        val c = typeParamToString( params( 3 ) )
        s"def bar2[$p,$a,$b,$c](p1: $p => Boolean)(p2: $a => $c)(p3: $b => $c): $c = {???}"
        */
      case Const( "pair", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pair[$a,$b](p0: $a)(p1: $b): Tuple2[$a,$b] = (p0, p1)"
      case Const( "pi1", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pi1[$a,$b](p: ($a,$b)) = p._1"
      case Const( "pi2", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pi2[$a,$b](p: ($a,$b)) = p._2"
      case Const( "inl", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val res = ( if ( !definedSumType ) s"sealed trait Sum[$a,$b]\n" else "" ) +
          s"final case class Inl[$a,$b](v:$a) extends Sum[$a,$b]\n" +
          s"def inl[$a, $b]( v: $a ): Sum[$a,$b] = new Inl( v )"
        definedSumType = true
        res
      case Const( "inr", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val res = ( if ( !definedSumType ) s"sealed trait Sum[$a,$b]\n" else "" ) +
          s"final case class Inr[$a,$b](v:$b) extends Sum[$a,$b]\n" +
          s"def inr[$a, $b]( v: $b ): Sum[$a,$b] = new Inr( v )"

        definedSumType = true
        res
      case Const( "matchSum", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val c = typeParamToString( params( 2 ) )
        val res = ( if ( !definedSumType ) s"sealed trait Sum[$a,$b]\n" else "" ) +
          s"""
def matchSum[$a,$b,$c](p1: Sum[$a,$b])(p2: $a => $c)(p3: $b => $c) = {
  p1 match {
    case Inl(a) => p2(a)
    case Inr(b) => p3(b)
    }
  }
"""
        definedSumType = true
        res
      case Const( "s", _, params ) =>
        s"def s(x: Int) = x + 1"
      case Const( "efq", _, params ) =>
        s"def efq(p: Throwable) = {throw p}"
      case Const( "exception", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        s"class NewException[$a](m: $a) extends Exception { def getVal: $a = m }\n" +
          s"def exception[$a](p: $a) = {new NewException(p)}"
      case Const( "pow2", _, params ) =>
        s"def pow2(x: Int) = x * x"
      case Const( "*", _, params ) =>
        s"def mul(x: Int)(y: Int) = x * y"
      case Const( "<=", _, params ) =>
        s"def leq(x: Int)(y: Int) = x <= y"
      case Const( "<", _, params ) =>
        s"def lt(x: Int)(y: Int) = x < y"
      case Const( "=", _, params ) =>
        val x = typeParamToString( params( 0 ) )
        s"def eq[$x](x: $x)(y: $x) = x == y"
      // TODO
      case Const( "f", _, params ) =>
        s"def f(x: Int)(y: Int) = x < (y+1)*(y+1) && y*y <= x"
      case Const( "natRec", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        s"""
def natRec[$a](p1: $a)(p2: (Int => $a => $a))(p3: Int): $a = {
if(p3 == 0) {
  p1
} else {
  p2(p3-1)(natRec(p1)(p2)(p3-1))
}
}"""
      case c @ _ =>
        ""
      //"not yet implemented: " + c.toString
    }.mkString( "\n" )
    prefix + definitions + suffix
  }

  def toTerm( c: Const ): String = {
    c match {
      case Const( "i", _, _ )  => "()"
      case Const( "*", _, _ )  => "mul"
      case Const( "<=", _, _ ) => "leq"
      case Const( "<", _, _ )  => "lt"
      case Const( "=", _, _ )  => "eq"
      //TODO: and/or/impl etc.
      /*
      case Const( "pi1", _, params ) =>
        s"pi1[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "pi2", _, params ) =>
        s"pi2[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "natRec", _, params ) =>
        s"natRec[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "pair", _, params ) =>
        s"pair[${params.map( toType( _ ) ).mkString( "," )}]"
        */
      case Const( "inl", _, params ) =>
        s"inl[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "inr", _, params ) =>
        s"inr[${params.map( toType( _ ) ).mkString( "," )}]"
      /*
      case Const( "exception", _, params ) =>
        s"exception[${params.map( toType( _ ) ).mkString( "," )}]"
        */
      case _ => c.name
    }
  }

  def toType( t: Ty ): String = {
    t match {
      case TBase( "1", Nil ) => "Unit"
      case TBase( "nat", Nil )
        | TBase( "i", Nil ) => "Int"
      case TBase( "o", Nil )       => "Boolean"
      case TBase( "exn", Nil )     => "Exception"
      case TBase( "conj", params ) => s"Tuple2[${toType( params( 0 ) )}, ${toType( params( 1 ) )}]"
      case TBase( "sum", params )  => s"Sum[${toType( params( 0 ) )}, ${toType( params( 1 ) )}]"
      case TArr( t1, t2 )          => s"(${toType( t1 )} => ${toType( t2 )})"
      case _                       => t.toString
    }
  }

  def translate( e: Expr )( implicit ctx: Context ): String = {
    e match {
      case App( App( App( Const( "bar2", _, params ), _ ), catchTerm ), tryTerm ) =>
        val a = toType( params( 1 ) )
        s"""
           |try {
           |  ${translate( tryTerm )}(exception)
           |} catch {
           |  case e: NewException[$a] => ${translate( catchTerm )}(e.getVal)
           |  case e => println("BUG"); throw e
           |}
         """.stripMargin
      case App( e1, e2 ) =>
        s"${translate( e1 )}(${translate( e2 )})"
      case Abs( v, e ) =>
        s"({\n  ${v.name} : ${toType( v.ty )} => ${translate( e )}})"
      case Var( name, _ ) =>
        name
      case c: Const =>
        toTerm( c )
    }
  }
}
