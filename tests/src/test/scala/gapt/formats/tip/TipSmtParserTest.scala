package gapt.formats.tip

import gapt.expr.hol.instantiate
import gapt.expr.{ Const, TBase }
import gapt.formats.ClasspathInputFile
import gapt.formats.lisp.SExpressionParser
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem = TipSmtImporter.parse( ClasspathInputFile( "bin_distrib.smt2" ) )
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
    parser.TipSmtParser.parse( Seq( dummyDatatype ) )
    parser.TipSmtParser.parse( Seq( constantDeclaration ) )
    success
  }

  val sortDeclaration = new SExpressionParser(
    "(declare-sort sort :attr1 :attr2 val2 :attr3 0)" ).SExpr.run().get

  "sort declaration should succeed" in {
    parser.TipSmtParser.parse( Seq( sortDeclaration ) )
    success
  }

  val datatypeDeclaration = new SExpressionParser(
    "(declare-datatypes () ((nat :attr1 val1 (z :attr2) (s :attr3 val3 :attr4 (p nat) ) )) )" ).SExpr.run().get

  "datatype declaration should succeed" in {
    parser.TipSmtParser.parse( Seq( datatypeDeclaration ) )
    success
  }

  val recursiveFunctionDefinition = new SExpressionParser(
    "(define-fun-rec fun :attr1 val1 :attr2 :attr3 val3 () t c)" ).SExpr.run().get

  "recursive function definition should succeed" in {
    parser.TipSmtParser.parse( Seq( dummyDatatype ) )
    parser.TipSmtParser.parse( Seq( recursiveFunctionDefinition ) )
    success
  }

  val functionDefinition = new SExpressionParser(
    "(define-fun fun :attr1 val1 :attr2 :attr3 val3 () t c)" ).SExpr.run().get

  "function definition" in {
    parser.TipSmtParser.parse( Seq( dummyDatatype ) )
    parser.TipSmtParser.parse( Seq( functionDefinition ) )
    success
  }

  val functionDeclaration = new SExpressionParser(
    "(declare-fun fun :attr1 () t)" ).SExpr.run().get

  "function declaration should succeed" in {
    parser.TipSmtParser.parse( Seq( dummyDatatype ) )
    parser.TipSmtParser.parse( Seq( functionDeclaration ) )
    success
  }

  val assertion1 = new SExpressionParser(
    "(assert :attr true)" ).SExpr.run().get

  val assertion2 = new SExpressionParser(
    "(prove :attr value true)" ).SExpr.run().get

  "parsing assertions should succeed" in {
    "assert assertion" in {
      parser.TipSmtParser.parse( Seq( assertion1 ) )
      success
    }
    "prove assertion" in {
      parser.TipSmtParser.parse( Seq( assertion2 ) )
      success
    }
  }
}
