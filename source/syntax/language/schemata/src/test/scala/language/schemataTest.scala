package at.logic.language.schemata

import at.logic.language.lambda.symbols._
import org.specs._
import org.specs.runner._

import at.logic.language.schemata._

class schemaTest extends SpecificationWithJUnit {


  println("\n\n\n\n")

  val v = IntVar((new VariableStringSymbol("a")).asInstanceOf[VariableSymbolA])
  val c  = IntConst() // equivalent to calling IntConst.apply() (on the object)
  val sch = Succ(Succ(c))
  println("\n"+sch.toString)
  println("\n\n\n\n")
  0 must beEqual (0)

}