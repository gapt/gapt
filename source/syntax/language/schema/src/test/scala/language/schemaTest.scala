package at.logic.language.schema

import at.logic.language.lambda.typedLambdaCalculus.App
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import org.specs._
import org.specs.runner._

import at.logic.language.schema._

class schemaTest extends SpecificationWithJUnit {


  println("\n\n\n\n")

  val v = IntVar((new VariableStringSymbol("a")).asInstanceOf[VariableSymbolA])
  val c  = IntConst() // equivalent to calling IntConst.apply() (on the object)
  val sch = Succ(Succ(c))
  println("\n"+sch.toString)
  val iv1 = IndexedPredicate((new VariableStringSymbol("P1")).asInstanceOf[VariableSymbolA], c, To())
  val iv2 = IndexedPredicate((new VariableStringSymbol("P2")).asInstanceOf[VariableSymbolA], sch, To())
  val and12 = SAnd(iv1.asInstanceOf[SchemaFormula], iv2.asInstanceOf[SchemaFormula])
  println("\n"+and12.toString)
  println("\n\n\n\n")
  0 must beEqual (0)

}