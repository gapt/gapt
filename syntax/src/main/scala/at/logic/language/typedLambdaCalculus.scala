/*
 * typedLambdaCalculus.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

/**
 * Implementation representing a symbol which is a string
 * @param name the value of the name
 */
case class Name(name: String) extends SymbolA 

object NameImplicitConverters {
    implicit def toName(s: String) = Name(s)
}

case class Var[+T <: TA](override val symbol: SymbolA ) extends LambdaVarA[T](symbol)

case class Abs[+T1 <: TA, +T2 <: TA](override val variable: LambdaVarA[T1], override val expression: LambdaExpressionA[T2] )
    extends LambdaAbstractionA[T1, T2](variable, expression)

case class App[+T1 <: TA, +T2 <: TA](override val function: LambdaExpressionA[TArrow[T1, T2]], override val argument: LambdaExpressionA[T1] ) extends LambdaApplicationA[T1, T2](function, argument)


object B {
    import NameImplicitConverters._
    def f = {
        val b = Var[TInd]("p")
        val a = Abs(Var[TInd](Name("a")), App( Var[TArrow[TInd,TBool]](Name("P")), Var[TInd](Name("a"))) )
        println("hello")
    }
}