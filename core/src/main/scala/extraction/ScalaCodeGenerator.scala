package extraction

import gapt.expr._
import gapt.proofs.Context

object ScalaCodeGenerator {
  def apply = new ScalaCodeGenerator( "extracted" )

  def apply( name: String ) = new ScalaCodeGenerator( name )
}

class ScalaCodeGenerator( name: String ) extends CodeGenerator( name ) {

  val prefix =
    s"""
      |object $name extends Script {
      |""".stripMargin

  val postfix = "\n}"

  def generateBoilerPlate( e: Expr )( implicit context: Context ): String = {
    def typeParamToString( param: Ty ) = param.toString.substring( 1 ).toUpperCase()

    var definedSumType = false

    context.constants.filter {
      case Const( "i", _, _ )
        | Const( "0", _, _ ) => false
      case _ => true
    }.map {
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
          s"final case class Inl[$a,$b](v:$a) extends Sum[$a,$b]\n"
        definedSumType = true
        res
      case Const( "inr", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val res = ( if ( !definedSumType ) s"sealed trait Sum[$a,$b]\n" else "" ) +
          s"final case class Inr[$a,$b](v:$b) extends Sum[$a,$b]\n"
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
      case Const( "existsElim", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        val b = typeParamToString( params( 1 ) )
        val c = typeParamToString( params( 2 ) )
        s"def existsElim[$a,$b,$c](p1: Tuple2[$a,$b])(p2: $a => $b => $c) = p2( p1._1 )( p1._2 )"
      case Const( "s", _, params ) =>
        s"def s(x: Int) = x + 1"
      /*
      case Const( "raise", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        s"def raise[$a](x: $a): Exception = throw exception(x)(None) // TODO get name/id of hypothesis variable in extraction"
      */
      case Const( "efq", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        s"def efq[$a](p: Throwable): $a = throw p"
      case Const( "exception", _, params ) =>
        val a = typeParamToString( params( 0 ) )
        s"""
case class Exn[$a](v: $a, id: Option[Int]) extends Exception
def exception[$a](v: $a )(id: Option[Int] = None) = new Exn(v, id)"""
      case Const( "pow2", _, params ) =>
        s"def pow2(x: Int) = x * x"
      case Const( "<=", _, params ) =>
        s"def leq(x: Int)(y: Int) = x <= y"
      case Const( "<", _, params ) =>
        s"def lt(x: Int)(y: Int) = x < y"
      case Const( "=", _, params ) =>
        val x = typeParamToString( params( 0 ) )
        s"def eq[$x](x: $x)(y: $x) = x == y"
      case Const( "*", _, params ) =>
        s"def mul(x: Int)(y: Int) = x * y"
      case Const( "+", _, params ) =>
        s"def add(x: Int)(y: Int) = x + y"
      case Const( "-", _, params ) =>
        s"def sub(x: Int)(y: Int) = x - y"
      // TODO
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
    }.filterNot( _ == "" ).mkString( "\n" )
  }

  def toTerm( c: Const ): String = {
    c match {
      case Const( "i", _, _ )  => "()"
      case Const( "<=", _, _ ) => "leq"
      case Const( "<", _, _ )  => "lt"
      case Const( "=", _, _ )  => "eq"
      case Const( "*", _, _ )  => "mul"
      case Const( "+", _, _ )  => "add"
      case Const( "-", _, _ )  => "sub"
      //TODO: and/or/impl etc.
      case Const( "pi1", _, params ) =>
        s"pi1[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "pi2", _, params ) =>
        s"pi2[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "existsElim", _, params ) =>
        s"existsElim[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "natRec", _, params ) =>
        s"natRec[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "pair", _, params ) =>
        s"pair[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "efq", _, params ) =>
        s"efq[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "inl", _, params ) =>
        s"Inl[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "inr", _, params ) =>
        s"Inr[${params.map( toType( _ ) ).mkString( "," )}]"
      case Const( "exception", _, params ) =>
        s"exception[${params.map( toType( _ ) ).mkString( "," )}]"
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
      //case TBase( "exn", params )  => s"Exn[${toType( params( 0 ) )}"
      case TBase( "conj", params ) => s"Tuple2[${toType( params( 0 ) )}, ${toType( params( 1 ) )}]"
      case TBase( "sum", params )  => s"Sum[${toType( params( 0 ) )}, ${toType( params( 1 ) )}]"
      case TArr( t1, t2 )          => s"(${toType( t1 )} => ${toType( t2 )})"
      case _                       => t.toString
    }
  }

  var bugID = 0
  def translate( e: Expr )( implicit ctx: Context ): String = {
    e match {
      // TODO: catchTerm using handle
      case App( App( Const( "tryCatch", _, params ), catchTerm ), tryTerm ) =>
        val localBugID = bugID
        bugID = bugID + 1
        val a = toType( params( 0 ) )
        s"""
           |try {
           |  ${translate( tryTerm )}(exception[$a]( _ )( Some( $localBugID ) ) )
           |} catch {
           |  case Exn( v : $a, Some( id ) ) if id == $localBugID => {
           |    //println( "thrown at " + id + " caught at $localBugID" )
           |    ${translate( catchTerm )}( v )
           |  }
           |  case e => {
           |    //println("throwing further at $localBugID")
           |    throw e
           |  }
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
