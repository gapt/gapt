package at.logic.gapt.formats.tip

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr.{ Const, TBase }
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.lisp.SExpressionParser
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable._

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem = TipSmtParser.parse( ClasspathInputFile( "bin_distrib.smt2" ) )
    val one = Const( "One", TBase( "Bin" ) )
    val oneAnd = Const( "OneAnd", TBase( "Bin" ) ->: TBase( "Bin" ) )
    val instanceSequent = problem.toSequent.map( identity, instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Escargot getResolutionProof instanceSequent must beSome
  }

  val constantDeclaration = new SExpressionParser(
    "(declare-const constant :attr1 t)" ).SExpr.run().get

  val dummyDatatype = new SExpressionParser(
    "(declare-datatypes () ((t (c))))" ).SExpr.run().get

  "constant declaration should succeed" in {
    val tipSmtParser = new TipSmtParser()
    tipSmtParser.parse( dummyDatatype )
    tipSmtParser.parse( constantDeclaration )
    success
  }

  val sortDeclaration = new SExpressionParser(
    "(declare-sort sort :attr1 :attr2 val2 :attr3 0)" ).SExpr.run().get

  "sort declaration should succeed" in {
    new TipSmtParser().parse( sortDeclaration )
    success
  }

  val datatypeDeclaration = new SExpressionParser(
    "(declare-datatypes () ((nat :attr1 val1 (z :attr2) (s :attr3 val3 :attr4 (p nat) ) )) )" ).SExpr.run().get

  "datatype declaration should succeed" in {
    new TipSmtParser().parse( datatypeDeclaration )
    success
  }

  val recursiveFunctionDefinition = new SExpressionParser(
    "(define-fun-rec fun :attr1 val1 :attr2 :attr3 val3 () t c)" ).SExpr.run().get

  "recursive function definition should succeed" in {
    val tipSmtParser = new TipSmtParser()
    tipSmtParser.parse( dummyDatatype )
    tipSmtParser.parse( recursiveFunctionDefinition )
    success
  }

  val functionDefinition = new SExpressionParser(
    "(define-fun fun :attr1 val1 :attr2 :attr3 val3 () t c)" ).SExpr.run().get

  "function definition" in {
    val tipSmtParser = new TipSmtParser()
    tipSmtParser.parse( dummyDatatype )
    tipSmtParser.parse( functionDefinition )
    success
  }

  val functionDeclaration = new SExpressionParser(
    "(declare-fun fun :attr1 () t)" ).SExpr.run().get

  "function declaration should succeed" in {
    val tipSmtParser = new TipSmtParser()
    tipSmtParser.parse( dummyDatatype )
    tipSmtParser.parse( functionDeclaration )
    success
  }

  val assertion1 = new SExpressionParser(
    "(assert :attr true)" ).SExpr.run().get

  val assertion2 = new SExpressionParser(
    "(prove :attr value true)" ).SExpr.run().get

  "parsing assertions should succeed" in {
    "assert assertion" in {
      new TipSmtParser().parse( assertion1 )
      success
    }
    "prove assertion" in {
      new TipSmtParser().parse( assertion2 )
      success
    }
  }
}
