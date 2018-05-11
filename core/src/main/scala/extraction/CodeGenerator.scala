package extraction

import gapt.expr._
import gapt.proofs.Context

object CodeGenerator {

  def apply( e: Expr, ctx: Context ) = {
    println( ctx )
    println( generateBoilerPlate( ctx ) )
    println( translateLambda( e ) )
  }

  private def generateBoilerPlate( context: Context ) = {
    def typeParamToString( param: Ty ) = param.toString.substring( 1 ).toUpperCase()

    var definedSumType = false
    context.constants.map {
      case Const( "bar", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val c = typeParamToString( params( 2 ) )
        s"def bar[$a,$b,$c](p1: Function[$a,$c])(p2:Function[$b,$c]) = {???}"
      case Const( "pair", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pair[$a,$b](p0: $a)(p1: $b) = (p0, p1)"
      case Const( "pi1", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pi1[$a,$b](p: Tuple2[$a,$b]) = p._1"
      case Const( "pi2", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        s"def pi2[$a,$b](p: Tuple2[$a,$b]) = p._2"
      case Const( "inl", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val res = ( if ( !definedSumType ) s"sealed trait sum[$a,$b]\n" else "" ) +
          s"final case class inl[$a,$b](v:$a) extends sum[$a,$b]"
        definedSumType = true
        res
      case Const( "inr", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val res = ( if ( !definedSumType ) s"sealed trait sum[$a,$b]\n" else "" ) +
          s"final case class inr[$a,$b](v:$a) extends sum[$a,$b]"
        definedSumType = true
        res
      case Const( "matchSum", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val c = typeParamToString( params( 2 ) )
        val res = ( if ( !definedSumType ) s"sealed trait sum[$a,$b]\n" else "" ) +
          s"""
def matchSum[$a,$b,$c](p1: sum[$a,$b])(p2: Function[$a,$c])(p3: Function[$b,$c]) = {
  p1 match {
    case inl(a) => p2(a)
    case inr(b) => p3(b)
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
        s"class NewException[$a](m: $a) extends Exception\n" +
          s"def exception[$a](p: $a) = {new NewException(p)}"
      case e @ _ =>
        "not yet implemented: " + e.toString
    }.mkString( "\n" )
  }

  private def toScalaType( t: Ty ): String = {
    t match {
      case TBase( "1", Nil )       => "Nothing"
      case TBase( "nat", Nil )     => "Int"
      case TBase( "exn", Nil )     => "Exception"
      case TBase( "conj", params ) => s"Tuple2[${toScalaType( params( 0 ) )}, ${toScalaType( params( 1 ) )}]"
      case TBase( "sum", params )  => s"sum[${toScalaType( params( 0 ) )}, ${toScalaType( params( 1 ) )}]"
      case TArr( t1, t2 )          => s"Function[${toScalaType( t1 )}, ${toScalaType( t2 )}]"
      case _                       => t.toString
    }
  }

  private def translateLambda( e: Expr ): String = {
    e match {
      case App( e1, e2 ) =>
        s"${translateLambda( e1 )}(${translateLambda( e2 )})\n"
      case Abs( v, e ) =>
        val vScalaType = toScalaType( v.ty )
        s"{${v.name} : $vScalaType => ${translateLambda( e )}}\n"
      case Var( name, _ ) =>
        name
      case Const( name, _, _ ) =>
        name
      case _ =>
        ???
    }
  }

  def test2[A, B, C]( p: Function[A, B] ) = {}

  def test[A, B]( p1: A, p2: B ) = {
  }

}
