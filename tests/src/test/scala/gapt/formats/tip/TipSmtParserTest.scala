package gapt.formats.tip

import gapt.expr.hol.instantiate
import gapt.expr.{ Const, TBase }
import gapt.formats.ClasspathInputFile
import gapt.formats.lisp.LSymbol
import gapt.formats.lisp.SExpressionParser
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtCheckSat
import gapt.formats.tip.parser.TipSmtConstantDeclaration
import gapt.formats.tip.parser.TipSmtConstructor
import gapt.formats.tip.parser.TipSmtConstructorField
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDatatype
import gapt.formats.tip.parser.TipSmtDatatypesDeclaration
import gapt.formats.tip.parser.TipSmtDistinct
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFormalParameter
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDeclaration
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtKeyword
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtParserException
import gapt.formats.tip.parser.TipSmtSortDeclaration
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtType
import gapt.formats.tip.parser.TipSmtVariableDecl
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

  "expression parser" in {
    "parsing and-expression" in {
      "parsing well-formed and-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(and t1 t2)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtAnd(
              Seq( TipSmtIdentifier( "t1" ), TipSmtIdentifier( "t2" ) ) )
        }
        "empty list of arguments" in {
          val input = new SExpressionParser(
            "(and)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtAnd( Seq() )
        }
      }
      "parsing ill-formed and-expression should throw exception" in {
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(and t1 ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing or-expression" in {
      "parsing well-formed or-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(or t1 t2)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtOr(
              Seq( TipSmtIdentifier( "t1" ), TipSmtIdentifier( "t2" ) ) )
        }
        "empty list of arguments" in {
          val input = new SExpressionParser(
            "(or)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtOr( Seq() )
        }
      }
      "parsing ill-formed or-expression should throw exception" in {
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(or t1 ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing imp-expression" in {
      "parsing well-formed imp-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(=> t1 t2)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtImp( Seq( TipSmtIdentifier( "t1" ), TipSmtIdentifier( "t2" ) ) )
        }
        "empty list of arguments" in {
          val input = new SExpressionParser(
            "(=>)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtImp( Seq() )
        }
      }
      "parsing ill-formed imp-expression should throw exception" in {
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(=> t1 ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing eq-expression" in {
      "parsing well-formed eq-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(= t1 t2)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtEq( Seq( TipSmtIdentifier( "t1" ), TipSmtIdentifier( "t2" ) ) )
        }
        "empty list of arguments" in {
          val input = new SExpressionParser(
            "(=)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtEq( Seq() )
        }
      }
      "parsing ill-formed eq-expression should throw exception" in {
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(= t1 ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing forall-expression" in {
      "parsing well-formed forall-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(forall ((x1 a1)) t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtForall(
              Seq( TipSmtVariableDecl( "x1", TipSmtType( "a1" ) ) ),
              TipSmtIdentifier( "t1" ) )
        }
        "empty list of variables" in {
          val input = new SExpressionParser(
            "(forall () t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtForall( Seq(), TipSmtIdentifier( "t1" ) )
        }
      }
      "parsing ill-formed forall-expression should throw exception" in {
        "missing variable list" in {
          val input = new SExpressionParser(
            "(forall t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "ill-formed variable list" in {
          val input = new SExpressionParser(
            "(forall vars t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "missing expression" in {
          val input = new SExpressionParser(
            "(forall ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(forall (x b) ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing exists-expression" in {
      "parsing well-formed exists-expression should succeed" in {
        "non-empty list of arguments" in {
          val input = new SExpressionParser(
            "(exists ((x1 a1)) t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtExists(
              Seq( TipSmtVariableDecl( "x1", TipSmtType( "a1" ) ) ),
              TipSmtIdentifier( "t1" ) )
        }
        "empty list of variables" in {
          val input = new SExpressionParser(
            "(exists () t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtExists( Seq(), TipSmtIdentifier( "t1" ) )
        }
      }
      "parsing ill-formed exists-expression should throw exception" in {
        "missing variable list" in {
          val input = new SExpressionParser(
            "(exists t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "ill-formed variable list" in {
          val input = new SExpressionParser(
            "(exists vars t1)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "missing expression" in {
          val input = new SExpressionParser(
            "(exists ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "subexpression is ill-formed" in {
          val input = new SExpressionParser(
            "(exists (x b) ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
    "parsing distinct-expression" in {
      "parsing well-formed distinct-expression should succeed" in {
        "non-empty list of subexpressions" in {
          val input = new SExpressionParser(
            "(distinct t1 t2 t3)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtDistinct(
              Seq(
                TipSmtIdentifier( "t1" ),
                TipSmtIdentifier( "t2" ),
                TipSmtIdentifier( "t3" ) ) )
        }
        "empty list of subexpressions" in {
          val input = new SExpressionParser(
            "(distinct)" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must_==
            TipSmtDistinct( Seq() )
        }
      }
      "parsing ill-formed distinct-expression should throw exception" in {
        "ill-formed subexpression" in {
          val input = new SExpressionParser(
            "(distinct ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
      }
    }
  }
  "parsing if-then-else-expression" in {
    "parsing well-formed ite-expression should succeed" in {
      val input = new SExpressionParser(
        "(ite t1 t2 t3)" ).SExpr.run().get
      parser.TipSmtParser.parseExpression( input ) must_==
        TipSmtIte(
          TipSmtIdentifier( "t1" ),
          TipSmtIdentifier( "t2" ),
          TipSmtIdentifier( "t3" ) )
    }
    "parsing ill-formed ite-expression should throw exception" in {
      "ill-formed condition" in {
        val input = new SExpressionParser(
          "(ite () t2 t3)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed ifTrue" in {
        val input = new SExpressionParser(
          "(ite t1 () t3)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed ifFalse" in {
        val input = new SExpressionParser(
          "(ite t1 t2 ())" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
    }
  }
  "parsing not-expression" in {
    "parsing well-formed not-expression should succeed" in {
      val input = new SExpressionParser(
        "(not t1)" ).SExpr.run().get
      parser.TipSmtParser.parseExpression( input ) must_==
        TipSmtNot( TipSmtIdentifier( "t1" ) )
    }
    "parsing ill-formed not-expression should throw exception" in {
      "no subexpression" in {
        val input = new SExpressionParser(
          "(not)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "more than one subexpression" in {
        val input = new SExpressionParser(
          "(not t1 t2)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed subexpression" in {
        val input = new SExpressionParser(
          "(not ())" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
    }
  }
  "parsing function call-expression" in {
    "parsing well-formed function call-expression should succeed" in {
      "empty argument list" in {
        val input = new SExpressionParser(
          "(f)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must_==
          TipSmtFun( "f", Seq() )
      }
      "non-empty argument list" in {
        val input = new SExpressionParser(
          "(f a1 a2 a3)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must_==
          TipSmtFun(
            "f",
            Seq(
              TipSmtIdentifier( "a1" ),
              TipSmtIdentifier( "a2" ),
              TipSmtIdentifier( "a3" ) ) )
      }
      "parsing ill-formed fun. call-expr should not return fun. expr." in {
        "ill-formed argument should throw exception" in {
          val input = new SExpressionParser(
            "(f a1 a2 ())" ).SExpr.run().get
          parser.TipSmtParser.parseExpression( input ) must
            throwA[TipSmtParserException]
        }
        "function name is reserved word should return other object or throw" in
          {
            val input = new SExpressionParser(
              "(not a1 a2 a3)" ).SExpr.run().get
            parser.TipSmtParser.parseExpression( input ) must
              throwA[TipSmtParserException]

          }
      }
    }
  }
  "parsing identifier-expression" in {
    "non reserved identifier should succeed" in {
      val input = new SExpressionParser( "f" ).SExpr.run().get
      parser.TipSmtParser.parseExpression( input ) must_==
        TipSmtIdentifier( "f" )
    }
  }
  "parsing match-expression" in {
    "parsing well-formed match-expression should succeed" in {
      "non-empty sequence of cases" in {
        val input = new SExpressionParser(
          "(match t (case c1 e1) (case c2 e2))" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must_==
          TipSmtMatch(
            TipSmtIdentifier( "t" ),
            Seq(
              TipSmtCase(
                TipSmtConstructorPattern( TipSmtIdentifier( "c1" ), Seq() ),
                TipSmtIdentifier( "e1" ) ),
              TipSmtCase(
                TipSmtConstructorPattern( TipSmtIdentifier( "c2" ), Seq() ),
                TipSmtIdentifier( "e2" ) ) ) )
      }
      "empty sequence of case statements" in {
        val input = new SExpressionParser(
          "(match t)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must_==
          TipSmtMatch( TipSmtIdentifier( "t" ), Seq() )
      }
    }
    "parsing ill-formed match-expression should throw exception" in {
      "ill-formed match expression" in {
        val input = new SExpressionParser(
          "(match () (case c1 e1) (case c2 e2))" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed case statements" in {
        val input = new SExpressionParser(
          "(match t a)" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed pattern" in {
        val input = new SExpressionParser(
          "(match t ( (case () e1) (case c2 e2) ))" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
      "ill-formed case expression" in {
        val input = new SExpressionParser(
          "(match t (case c1 e1) (case c2 (not a b)) )" ).SExpr.run().get
        parser.TipSmtParser.parseExpression( input ) must
          throwA[TipSmtParserException]
      }
    }
  }
  "parsing true should succeed" in {
    parser.TipSmtParser.parseExpression( LSymbol( "true" ) ) must_== TipSmtTrue
  }
  "parsing false should succeed" in {
    parser.TipSmtParser.parseExpression( LSymbol( "false" ) ) must_==
      TipSmtFalse
  }
}

