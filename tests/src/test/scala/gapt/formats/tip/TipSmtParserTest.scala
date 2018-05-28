package gapt.formats.tip

import gapt.expr.hol.instantiate
import gapt.expr.{ Const, TBase }
import gapt.formats.ClasspathInputFile
import gapt.formats.lisp.SExpressionParser
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCheckSat
import gapt.formats.tip.parser.TipSmtConstantDeclaration
import gapt.formats.tip.parser.TipSmtConstructor
import gapt.formats.tip.parser.TipSmtConstructorField
import gapt.formats.tip.parser.TipSmtDatatype
import gapt.formats.tip.parser.TipSmtDatatypesDeclaration
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtFormalParameter
import gapt.formats.tip.parser.TipSmtFunctionDeclaration
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtKeyword
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtParserException
import gapt.formats.tip.parser.TipSmtSortDeclaration
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtType
import gapt.provers.escargot.Escargot
import org.specs2.mutable._

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem =
      TipSmtImporter.parse( ClasspathInputFile( "bin_distrib.smt2" ) )
    val one = Const( "One", TBase( "Bin" ) )
    val oneAnd = Const( "OneAnd", TBase( "Bin" ) ->: TBase( "Bin" ) )
    val instanceSequent =
      problem
        .toSequent
        .map(
          identity,
          instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Escargot getResolutionProof instanceSequent must beSome
  }

  val dummyDatatype = new SExpressionParser(
    "(declare-datatypes () ((t (c))))" ).SExpr.run().get

  "parsing constant declaration" in {

    "parsing well-formed constant declaration should succeed" in {
      val constantDeclaration = new SExpressionParser(
        "(declare-const constant :attr1 t)" ).SExpr.run().get

      val output = parser.TipSmtParser.parseCommand( constantDeclaration )

      output must beAnInstanceOf[TipSmtConstantDeclaration]

      val constant = output.asInstanceOf[TipSmtConstantDeclaration]

      constant.keywords must_== Seq( TipSmtKeyword( "attr1", None ) )
      constant.name must_== "constant"
      constant.typ must_== TipSmtType( "t" )
    }

    "parsing ill-formed constant declaration should throw exception" in {

      "type is missing" in {
        val constantDeclaration = new SExpressionParser(
          "(declare-const constant)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( constantDeclaration ) must
          throwA[TipSmtParserException]
      }

      "name is missing" in {
        val constantDeclaration = new SExpressionParser(
          "(declare-const :attr1 t)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( constantDeclaration ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing sort declaration" in {
    "parsing well-formed sort declaration should succeed" in {
      val sortDeclaration = new SExpressionParser(
        "(declare-sort sort :attr1 :attr2 val2 :attr3 0)" ).SExpr.run().get

      val output = parser.TipSmtParser.parseCommand( sortDeclaration )

      output must beAnInstanceOf[TipSmtSortDeclaration]

      val sort = output.asInstanceOf[TipSmtSortDeclaration]

      sort.keywords must_== Seq(
        TipSmtKeyword( "attr1", None ),
        TipSmtKeyword( "attr2", Some( "val2" ) ),
        TipSmtKeyword( "attr3", None ) )
      sort.name must_== "sort"
    }
    "parsing ill-formed sort declaration should throw exception" in {
      "sort number is missing" in {
        val sortDeclaration = new SExpressionParser(
          "(declare-sort sort :attr1 :attr2 val2 :attr3)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( sortDeclaration ) must
          throwA[TipSmtParserException]
      }
      "sort number is not an integer" in {
        val sortDeclaration = new SExpressionParser(
          "(declare-sort sort :attr1 :attr2 val2 :attr3 a)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( sortDeclaration ) must
          throwA[TipSmtParserException]
      }
      "sort name is missing" in {
        val sortDeclaration = new SExpressionParser(
          "(declare-sort :attr1 :attr2 val2 :attr3 0)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( sortDeclaration ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing datatype declaration" in {
    "parsing well-formed datatype declaration should succeed" in {
      val datatypeDeclaration = new SExpressionParser(
        """( declare-datatypes
          | ()
          | ((nat :attr1 val1 (z :attr2) (s :attr3 val3 :attr4 (p nat) ) ))
          | )""".stripMargin ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( datatypeDeclaration )

      output must beAnInstanceOf[TipSmtDatatypesDeclaration]

      val datatypeDecl = output.asInstanceOf[TipSmtDatatypesDeclaration]

      datatypeDecl.datatypes must_== Seq(
        TipSmtDatatype(
          "nat",
          Seq( TipSmtKeyword( "attr1", Some( "val1" ) ) ),
          Seq(
            TipSmtConstructor(
              "z",
              Seq( TipSmtKeyword( "attr2", None ) ), Seq() ),
            TipSmtConstructor(
              "s",
              Seq(
                TipSmtKeyword( "attr3", Some( "val3" ) ),
                TipSmtKeyword( "attr4", None ) ),
              Seq( TipSmtConstructorField( "p", TipSmtType( "nat" ) ) ) ) ) ) )
    }
    "parsing ill-formed datatype declaration should throw exception" in {
      "type parameter list is missing" in {
        val datatypeDeclaration = new SExpressionParser(
          """( declare-datatypes
            |
            | ((nat (z) (s (p nat) ) ))
            | )""".stripMargin ).SExpr.run().get
        parser
          .TipSmtParser
          .parseCommand( datatypeDeclaration ) must
          throwA[TipSmtParserException]
      }
      "some constructor is ill-formed" in {
        val datatypeDeclaration = new SExpressionParser(
          """( declare-datatypes
            |
            | ((nat () (s (p nat) ) ))
            | )""".stripMargin ).SExpr.run().get
        parser
          .TipSmtParser
          .parseCommand( datatypeDeclaration ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing recursive function definition" in {
    "parsing well-formed recursive function definition should succeed" in {
      val recursiveFunctionDefinition = new SExpressionParser(
        """(define-fun-rec
          | fun :attr1 val1 :attr2 :attr3 val3 ((x a) (y b)) t c)
          |""".stripMargin ).SExpr.run().get
      val output =
        parser.TipSmtParser.parseCommand( recursiveFunctionDefinition )
      output must beAnInstanceOf[TipSmtFunctionDefinition]
      val parsedFunctionDefinition =
        output.asInstanceOf[TipSmtFunctionDefinition]
      parsedFunctionDefinition.name must_== "fun"
      parsedFunctionDefinition.keywords must_== Seq(
        TipSmtKeyword( "attr1", Some( "val1" ) ),
        TipSmtKeyword( "attr2", None ),
        TipSmtKeyword( "attr3", Some( "val3" ) ) )
      parsedFunctionDefinition.parameters must_== Seq(
        TipSmtFormalParameter( "x", TipSmtType( "a" ) ),
        TipSmtFormalParameter( "y", TipSmtType( "b" ) ) )
      parsedFunctionDefinition.returnType must_== TipSmtType( "t" )
      parsedFunctionDefinition.body must_== TipSmtIdentifier( "c" )
    }

    "parsing ill-formed recursive function def. should throw exception" in {
      "function name is missing" in {
        val recursiveFunctionDefinition = new SExpressionParser(
          "(define-fun-rec ((x a) (y b)) t c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( recursiveFunctionDefinition ) must
          throwA[TipSmtParserException]
      }
      "formal parameters are missing" in {
        val recursiveFunctionDefinition = new SExpressionParser(
          "(define-fun-rec fun t c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( recursiveFunctionDefinition ) must
          throwA[TipSmtParserException]
      }
      "return type is missing" in {
        val recursiveFunctionDefinition = new SExpressionParser(
          "(define-fun-rec fun ((x a) (y b)) c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( recursiveFunctionDefinition ) must
          throwA[TipSmtParserException]
      }
      "body is missing" in {
        val recursiveFunctionDefinition = new SExpressionParser(
          "(define-fun-rec fun ((x a) (y b)) t)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( recursiveFunctionDefinition ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing function definition" in {
    "parsing well-formed function definition should succeed" in {
      val functionDefinition = new SExpressionParser(
        "(define-fun fun :attr1 val1 :attr2 :attr3 val3 ((x a) (y b)) t c)" ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( functionDefinition )
      output must beAnInstanceOf[TipSmtFunctionDefinition]
      val parsedFunctionDefinition =
        output.asInstanceOf[TipSmtFunctionDefinition]
      parsedFunctionDefinition.name must_== "fun"
      parsedFunctionDefinition.keywords must_== Seq(
        TipSmtKeyword( "attr1", Some( "val1" ) ),
        TipSmtKeyword( "attr2", None ),
        TipSmtKeyword( "attr3", Some( "val3" ) ) )
      parsedFunctionDefinition.parameters must_== Seq(
        TipSmtFormalParameter( "x", TipSmtType( "a" ) ),
        TipSmtFormalParameter( "y", TipSmtType( "b" ) ) )
      parsedFunctionDefinition.returnType must_== TipSmtType( "t" )
      parsedFunctionDefinition.body must_== TipSmtIdentifier( "c" )
    }
    "parsing ill-formed recursive function def. should throw exception" in {
      "function name is missing" in {
        val functionDefinition = new SExpressionParser(
          "(define-fun-rec ((x a) (y b)) t c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDefinition ) must
          throwA[TipSmtParserException]
      }
      "formal parameters are missing" in {
        val functionDefinition = new SExpressionParser(
          "(define-fun-rec fun t c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDefinition ) must
          throwA[TipSmtParserException]
      }
      "return type is missing" in {
        val functionDefinition = new SExpressionParser(
          "(define-fun-rec fun ((x a) (y b)) c)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDefinition ) must
          throwA[TipSmtParserException]
      }
      "body is missing" in {
        val functionDefinition = new SExpressionParser(
          "(define-fun-rec fun ((x a) (y b)) t)".stripMargin ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDefinition ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing function declaration" in {
    "parsing well-formed function declaration should succeed" in {
      val functionDeclaration = new SExpressionParser(
        "(declare-fun fun :attr1 () t)" ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( functionDeclaration )
      output must beAnInstanceOf[TipSmtFunctionDeclaration]
      val parsedDeclaration = output.asInstanceOf[TipSmtFunctionDeclaration]
      parsedDeclaration.name must_== "fun"
      parsedDeclaration.keywords must_== Seq( TipSmtKeyword( "attr1", None ) )
      parsedDeclaration.argumentTypes must_== Seq()
      parsedDeclaration.returnType must_== TipSmtType( "t" )
    }
    "parsing ill-typed function decl. should throw exception" in {
      "function name is missing" in {
        val functionDeclaration = new SExpressionParser(
          "(declare-fun () t)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDeclaration ) must
          throwA[TipSmtParserException]
      }
      "parameter type list is missing" in {
        val functionDeclaration = new SExpressionParser(
          "(declare-fun fun t)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDeclaration ) must
          throwA[TipSmtParserException]
      }
      "return type is missing" in {
        val functionDeclaration = new SExpressionParser(
          "(declare-fun fun ())" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( functionDeclaration ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing assertion" in {
    "parsing well-formed assertion should succeed" in {
      val assertion = new SExpressionParser(
        "(assert :attr true)" ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( assertion )
      output must beAnInstanceOf[TipSmtAssertion]
      val parsedAssertion = output.asInstanceOf[TipSmtAssertion]
      parsedAssertion.keywords must_== Seq( TipSmtKeyword( "attr", None ) )
      parsedAssertion.expr must_== TipSmtTrue
    }
    "parsing ill-formed assertion should throw exception" in {
      "expression is missing" in {
        val assertion = new SExpressionParser(
          "(assert :attr)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( assertion ) must
          throwA[TipSmtParserException]
      }
      "expression is ill-formed" in {
        val assertion = new SExpressionParser(
          "(assert :attr ())" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( assertion ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing goal" in {
    "parsing well-formed goal (assert-not) should succeed" in {
      val goal = new SExpressionParser(
        "(assert-not :attr false)" ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( goal )
      output must beAnInstanceOf[TipSmtGoal]
      val parsedAssertion = output.asInstanceOf[TipSmtGoal]
      parsedAssertion.keywords must_== Seq( TipSmtKeyword( "attr", None ) )
      parsedAssertion.expr must_== TipSmtFalse
    }
    "parsing well-formed goal (prove) should succeed" in {
      val goal = new SExpressionParser(
        "(prove :attr false)" ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( goal )
      output must beAnInstanceOf[TipSmtGoal]
      val parsedAssertion = output.asInstanceOf[TipSmtGoal]
      parsedAssertion.keywords must_== Seq( TipSmtKeyword( "attr", None ) )
      parsedAssertion.expr must_== TipSmtFalse
    }
    "parsing ill-formed goal should throw exception" in {
      "expression is missing (prove)" in {
        val goal = new SExpressionParser(
          "(prove :attr)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( goal ) must
          throwA[TipSmtParserException]
      }
      "expression is ill-formed (prove)" in {
        val goal = new SExpressionParser(
          "(prove :attr ())" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( goal ) must
          throwA[TipSmtParserException]
      }
      "expression is missing (assert-not)" in {
        val goal = new SExpressionParser(
          "(assert-not :attr)" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( goal ) must
          throwA[TipSmtParserException]
      }
      "expression is ill-formed (assert-not)" in {
        val goal = new SExpressionParser(
          "(assert-not :attr ())" ).SExpr.run().get
        parser.TipSmtParser.parseCommand( goal ) must
          throwA[TipSmtParserException]
      }
    }
  }

  "parsing mutually recursive function definitions" in {
    "parsing well-formed mutually recursive fun. defs. should succed" in {
      val funDefs = new SExpressionParser(
        """( define-funs-rec
            |(
            |(fun1 :attr1 val1 ((x a)) r1)
            |(fun2 ((y b)) r2))
            |(t1 t2))""".stripMargin ).SExpr.run().get
      val output = parser.TipSmtParser.parseCommand( funDefs )
      output must beAnInstanceOf[TipSmtMutualRecursiveFunctionDefinition]
      val parsedDefs =
        output.asInstanceOf[TipSmtMutualRecursiveFunctionDefinition]
      output must_== TipSmtMutualRecursiveFunctionDefinition(
        Seq(
          TipSmtFunctionDefinition(
            "fun1",
            Seq( TipSmtKeyword( "attr1", Some( "val1" ) ) ),
            Seq( TipSmtFormalParameter( "x", TipSmtType( "a" ) ) ),
            TipSmtType( "r1" ),
            TipSmtIdentifier( "t1" ) ),
          TipSmtFunctionDefinition(
            "fun2",
            Seq(),
            Seq( TipSmtFormalParameter( "y", TipSmtType( "b" ) ) ),
            TipSmtType( "r2" ),
            TipSmtIdentifier( "t2" ) ) ) )
    }
    "parsing ill-formed mutually rec. fun. defs. should throw exception" in {
      "ill-formed function signature" in {
        "function name is missing" in {
          val funDefs = new SExpressionParser(
            """( define-funs-rec
              |(
              |( ((x a)) r1)
              |(fun2 ((y b)) r2))
              |(t1 t2))""".stripMargin ).SExpr.run().get
          parser.TipSmtParser.parseCommand( funDefs ) must
            throwA[TipSmtParserException]
        }
        "formal parameters are missing" in {
          val funDefs = new SExpressionParser(
            """( define-funs-rec
              |(
              |(fun1 ((x a)) r1)
              |(fun2  r2))
              |(t1 t2))""".stripMargin ).SExpr.run().get
          parser.TipSmtParser.parseCommand( funDefs ) must
            throwA[TipSmtParserException]
        }
        "return type is missing" in {
          val funDefs = new SExpressionParser(
            """( define-funs-rec
              |(
              |(fun1 ((x a)) )
              |(fun2 ((y b)) r2))
              |(t1 t2))""".stripMargin ).SExpr.run().get
          parser.TipSmtParser.parseCommand( funDefs ) must
            throwA[TipSmtParserException]
        }
      }
      "different number of signatures and definitions" in {
        "more signatures than definitions" in {
          val funDefs = new SExpressionParser(
            """( define-funs-rec
              |(
              |(fun2 ((y b)) r2))
              |(t1 t2))""".stripMargin ).SExpr.run().get
          parser.TipSmtParser.parseCommand( funDefs ) must
            throwA[TipSmtParserException]
        }
        "more definitions than signatures" in {
          val funDefs = new SExpressionParser(
            """( define-funs-rec
              |(
              |(fun1 ((x a)) r1)
              |(fun2 ((y b)) r2))
              |(t1))""".stripMargin ).SExpr.run().get
          parser.TipSmtParser.parseCommand( funDefs ) must
            throwA[TipSmtParserException]
        }
      }
    }
  }

  "parsing check-sat command should succed" in {
    val checkSat = new SExpressionParser(
      "(check-sat)" ).SExpr.run().get
    parser.TipSmtParser.parseCommand( checkSat ) must
      beAnInstanceOf[TipSmtCheckSat]
  }
}

