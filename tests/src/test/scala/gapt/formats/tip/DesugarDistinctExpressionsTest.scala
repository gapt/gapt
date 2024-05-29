package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.desugarDistinctExpressions
import org.specs2.mutable.Specification

class DesugarDistinctExpressionsTest extends Specification {

  "distinct expressions should be desugared everywhere" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (distinct a b c) )
        | (define-funs-rec
        |   ( (f2 ((x nat)) nat) )
        |   ( (distinct a b c) ) )
        | (prove  (distinct a b c) )
        | (assert (distinct a b c) )
      """.stripMargin)
    )
    val resultingProblem =
      desugarDistinctExpressions.transform(originalProblem)

    originalProblem.definitions(1) must_!= resultingProblem.definitions(1)
    originalProblem.definitions(2) must_!= resultingProblem.definitions(2)
    originalProblem.definitions(3) must_!= resultingProblem.definitions(3)
    originalProblem.definitions(4) must_!= resultingProblem.definitions(4)
  }

  "distinct expressions should be desugared correctly" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (distinct a b c d) )
      """.stripMargin)
    )
    val resultingProblem =
      desugarDistinctExpressions.transform(originalProblem)

    val TipSmtAnd(expressions) =
      resultingProblem.definitions(1)
        .asInstanceOf[TipSmtFunctionDefinition]
        .body: @unchecked

    expressions.size must_== 6
    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("a"),
            TipSmtIdentifier("b")
          )
        )
      )
    ) must_== true

    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("a"),
            TipSmtIdentifier("c")
          )
        )
      )
    ) must_== true

    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("a"),
            TipSmtIdentifier("d")
          )
        )
      )
    ) must_== true

    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("b"),
            TipSmtIdentifier("c")
          )
        )
      )
    ) must_== true

    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("b"),
            TipSmtIdentifier("d")
          )
        )
      )
    ) must_== true

    expressions.contains(
      TipSmtNot(
        TipSmtEq(
          Seq(
            TipSmtIdentifier("c"),
            TipSmtIdentifier("d")
          )
        )
      )
    ) must_== true
  }
}
