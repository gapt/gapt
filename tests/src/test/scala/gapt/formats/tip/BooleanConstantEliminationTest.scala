package gapt.formats.tip

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtDefault
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtType
import gapt.formats.tip.transformation.eliminateBooleanConstants
import org.specs2.mutable._

class BooleanConstantEliminationTest extends Specification {
  "all expressions in problem should be simplified" in {
    val originalProblem =
      TipSmtProblem( Seq(
        TipSmtFunctionDefinition(
          "f",
          Nil,
          Nil,
          TipSmtType( "a" ),
          TipSmtAnd( TipSmtTrue :: TipSmtFalse :: Nil ) ),
        TipSmtMutualRecursiveFunctionDefinition( Seq(
          TipSmtFunctionDefinition(
            "g",
            Nil,
            Nil,
            TipSmtType( "a" ),
            TipSmtNot( TipSmtTrue ) ),
          TipSmtFunctionDefinition(
            "h",
            Nil,
            Nil,
            TipSmtType( "a" ),
            TipSmtEq( TipSmtTrue :: TipSmtIdentifier( "A" ) :: Nil ) ) ) ),
        TipSmtGoal(
          Nil,
          TipSmtOr( TipSmtTrue :: TipSmtFalse :: Nil ) ),
        TipSmtAssertion(
          Nil,
          TipSmtIte(
            TipSmtTrue,
            TipSmtIdentifier( "x" ),
            TipSmtIdentifier( "y" ) ) ) ) )
    eliminateBooleanConstants.transform( originalProblem ) must_==
      TipSmtProblem( Seq(
        TipSmtFunctionDefinition(
          "f",
          Nil,
          Nil,
          TipSmtType( "a" ),
          TipSmtFalse ),
        TipSmtMutualRecursiveFunctionDefinition( Seq(
          TipSmtFunctionDefinition(
            "g",
            Nil,
            Nil,
            TipSmtType( "a" ),
            TipSmtFalse ),
          TipSmtFunctionDefinition(
            "h",
            Nil,
            Nil,
            TipSmtType( "a" ),
            TipSmtIdentifier( "A" ) ) ) ),
        TipSmtGoal(
          Nil,
          TipSmtTrue ),
        TipSmtAssertion(
          Nil,
          TipSmtIdentifier( "x" ) ) ) )
  }

  "and-expression should be correctly simplified" in {
    "one sub-expression remaining" in {
      val expression = TipSmtAnd(
        TipSmtTrue :: TipSmtIdentifier( "A" ) :: TipSmtTrue :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtIdentifier( "A" ) ) ) )
    }
    "subexpressions contain false" in {
      val expression = TipSmtAnd(
        TipSmtTrue :: TipSmtIdentifier( "A" ) :: TipSmtFalse :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtFalse ) ) )
    }
    "true should be eliminated" in {
      val expression = TipSmtAnd(
        TipSmtTrue ::
          TipSmtIdentifier( "A" ) ::
          TipSmtTrue ::
          TipSmtIdentifier( "B" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtAnd(
              TipSmtIdentifier( "A" ) ::
                TipSmtIdentifier( "B" ) :: Nil ) ) ) )
    }
    "subexpressions should be simplified" in {
      val expression = TipSmtAnd(
        TipSmtIdentifier( "A" ) ::
          TipSmtAnd(
            TipSmtIdentifier( "C" ) ::
              TipSmtTrue ::
              TipSmtIdentifier( "B" ) :: Nil ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtAnd(
              TipSmtIdentifier( "A" ) ::
                TipSmtAnd(
                  TipSmtIdentifier( "C" ) ::
                    TipSmtIdentifier( "B" ) :: Nil ) :: Nil ) ) ) )
    }
  }

  "or-expression should be correctly simplified" in {
    "one sub-expression remaining" in {
      val expression = TipSmtOr(
        TipSmtFalse :: TipSmtIdentifier( "A" ) :: TipSmtFalse :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtIdentifier( "A" ) ) ) )
    }
    "subexpressions contain true" in {
      val expression = TipSmtOr(
        TipSmtTrue :: TipSmtIdentifier( "A" ) :: TipSmtFalse :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtTrue ) ) )
    }
    "false should be eliminated" in {
      val expression = TipSmtOr(
        TipSmtFalse ::
          TipSmtIdentifier( "A" ) ::
          TipSmtFalse ::
          TipSmtIdentifier( "B" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtOr(
              TipSmtIdentifier( "A" ) ::
                TipSmtIdentifier( "B" ) :: Nil ) ) ) )
    }
    "subexpressions should be simplified" in {
      val expression = TipSmtOr(
        TipSmtIdentifier( "A" ) ::
          TipSmtOr(
            TipSmtIdentifier( "C" ) ::
              TipSmtFalse ::
              TipSmtIdentifier( "B" ) :: Nil ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtOr(
              TipSmtIdentifier( "A" ) ::
                TipSmtOr(
                  TipSmtIdentifier( "C" ) ::
                    TipSmtIdentifier( "B" ) :: Nil ) :: Nil ) ) ) )
    }
  }

  "imp-expression should be correctly simplified" in {
    "true in negative polarity" in {
      val expression = TipSmtImp(
        TipSmtTrue :: TipSmtIdentifier( "A" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtIdentifier( "A" ) ) ) )
    }
    "true in positive polarity" in {
      val expression = TipSmtImp(
        TipSmtIdentifier( "A" ) :: TipSmtTrue :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtTrue ) ) )
    }
    "false in negative polarity" in {
      val expression = TipSmtImp(
        TipSmtFalse :: TipSmtIdentifier( "A" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtTrue ) ) )
    }
    "true in positive polarity" in {
      val expression = TipSmtImp(
        TipSmtIdentifier( "A" ) :: TipSmtFalse :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal( Nil, TipSmtNot( TipSmtIdentifier( "A" ) ) ) ) )
    }
    "subexpressions are right-associative" in {
      val expression = TipSmtImp(
        TipSmtIdentifier( "A" ) ::
          TipSmtTrue ::
          TipSmtIdentifier( "B" ) ::
          TipSmtFalse :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtImp( TipSmtIdentifier( "A" ) ::
              TipSmtNot( TipSmtIdentifier( "B" ) ) :: Nil ) ) ) )
    }

    "subexpressions should be simplified" in {
      val expression = TipSmtImp(
        TipSmtIdentifier( "A" ) ::
          TipSmtOr(
            TipSmtIdentifier( "C" ) ::
              TipSmtFalse ::
              TipSmtIdentifier( "B" ) :: Nil ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtImp(
              TipSmtIdentifier( "A" ) ::
                TipSmtOr(
                  TipSmtIdentifier( "C" ) ::
                    TipSmtIdentifier( "B" ) :: Nil ) :: Nil ) ) ) )
    }
  }

  "eq-expression should be correctly simplified" in {
    "subexpressions should be simplified" in {
      val expression = TipSmtEq(
        TipSmtIdentifier( "A" ) ::
          TipSmtOr(
            TipSmtIdentifier( "C" ) ::
              TipSmtFalse ::
              TipSmtIdentifier( "B" ) :: Nil ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtEq(
              TipSmtIdentifier( "A" ) ::
                TipSmtOr(
                  TipSmtIdentifier( "C" ) ::
                    TipSmtIdentifier( "B" ) :: Nil ) :: Nil ) ) ) )
    }
    "immediate subexpr. true should result in conjunction of subexprs." in {
      val expression = TipSmtEq(
        TipSmtTrue ::
          TipSmtIdentifier( "A" ) ::
          TipSmtIdentifier( "B" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtAnd(
              TipSmtIdentifier( "A" ) ::
                TipSmtIdentifier( "B" ) :: Nil ) ) ) )
    }
    "imm. subexpr. false should yield conjunction of negated subexpression" in {
      val expression = TipSmtEq(
        TipSmtFalse ::
          TipSmtIdentifier( "A" ) ::
          TipSmtIdentifier( "B" ) :: Nil )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtAnd(
              TipSmtNot( TipSmtIdentifier( "A" ) ) ::
                TipSmtNot( TipSmtIdentifier( "B" ) ) :: Nil ) ) ) )
    }
  }

  "forall-expression should be correctly simplified" in {
    "subexpressions should be simplified" in {
      val expression = TipSmtForall(
        Nil,
        TipSmtOr(
          TipSmtIdentifier( "C" ) ::
            TipSmtFalse ::
            TipSmtIdentifier( "B" ) :: Nil ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtForall(
              Nil,
              TipSmtOr(
                TipSmtIdentifier( "C" ) ::
                  TipSmtIdentifier( "B" ) :: Nil ) ) ) ) )
    }

    "imm. subexpr. true should eliminate quantifier" in {
      val expression = TipSmtForall( Nil, TipSmtTrue )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtTrue ) ) )
    }
    "imm. subexpr. false should eliminate quantifier" in {
      val expression = TipSmtForall( Nil, TipSmtFalse )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtFalse ) ) )
    }
  }

  "exists-expression should be correctly simplified" in {
    "subexpressions should be simplified" in {
      val expression = TipSmtExists(
        Nil,
        TipSmtOr(
          TipSmtIdentifier( "C" ) ::
            TipSmtFalse ::
            TipSmtIdentifier( "B" ) :: Nil ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtExists(
              Nil,
              TipSmtOr(
                TipSmtIdentifier( "C" ) ::
                  TipSmtIdentifier( "B" ) :: Nil ) ) ) ) )
    }

    "imm. subexpr. true should eliminate quantifier" in {
      val expression = TipSmtExists( Nil, TipSmtTrue )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtTrue ) ) )
    }
    "imm. subexpr. false should eliminate quantifier" in {
      val expression = TipSmtExists( Nil, TipSmtFalse )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtFalse ) ) )
    }
  }

  "not-expression should be correctly simplified" in {
    "subexpressions should be simplified" in {
      val expression = TipSmtNot(
        TipSmtOr(
          TipSmtIdentifier( "C" ) ::
            TipSmtFalse ::
            TipSmtIdentifier( "B" ) :: Nil ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtNot(
              TipSmtOr(
                TipSmtIdentifier( "C" ) ::
                  TipSmtIdentifier( "B" ) :: Nil ) ) ) ) )
    }
    "immediate subexpression true should yield false" in {
      val expression = TipSmtNot( TipSmtTrue )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtFalse ) ) )
    }

    "immediate subexpression false should yield true" in {
      val expression = TipSmtNot( TipSmtFalse )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtTrue ) ) )
    }
  }

  "ite-expression should be correctly simplified" in {
    "subexpressions should be simplified" in {
      val expression = TipSmtIte(
        TipSmtOr(
          TipSmtIdentifier( "C" ) ::
            TipSmtFalse ::
            TipSmtIdentifier( "B" ) :: Nil ),
        TipSmtAnd(
          TipSmtIdentifier( "C" ) ::
            TipSmtFalse ::
            TipSmtIdentifier( "B" ) :: Nil ),
        TipSmtNot( TipSmtFalse ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtIte(
              TipSmtOr(
                TipSmtIdentifier( "C" ) ::
                  TipSmtIdentifier( "B" ) :: Nil ),
              TipSmtFalse,
              TipSmtTrue ) ) ) )
    }

    "condition true should yield ifTrue" in {
      val expression = TipSmtIte(
        TipSmtTrue,
        TipSmtIdentifier( "B" ),
        TipSmtIdentifier( "C" ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtIdentifier( "B" ) ) ) )
    }

    "condition false should yield ifFalse" in {
      val expression = TipSmtIte(
        TipSmtFalse,
        TipSmtIdentifier( "B" ),
        TipSmtIdentifier( "C" ) )
      val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
      eliminateBooleanConstants.transform( problem ) must_==
        TipSmtProblem( Seq(
          TipSmtGoal(
            Nil,
            TipSmtIdentifier( "C" ) ) ) )
    }
  }

  "subexpression of match-expressions should be simplified" in {
    val expression = TipSmtMatch(
      TipSmtAnd( TipSmtTrue :: TipSmtIdentifier( "A" ) :: Nil ),
      Seq(
        TipSmtCase( TipSmtDefault, TipSmtNot( TipSmtTrue ) ) ) )
    val problem = TipSmtProblem( Seq( TipSmtGoal( Nil, expression ) ) )
    eliminateBooleanConstants.transform( problem ) must_==
      TipSmtProblem( Seq(
        TipSmtGoal(
          Nil,
          TipSmtMatch(
            TipSmtIdentifier( "A" ),
            Seq(
              TipSmtCase( TipSmtDefault, TipSmtFalse ) ) ) ) ) )
  }
}
