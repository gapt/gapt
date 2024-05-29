package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.eliminateRedundantQuantifiers
import org.specs2.mutable.Specification

class EliminateRedundantQuantifiersTest extends Specification {

  "useless quantifiers should be eliminated everywhere" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((y nat)) x) )
        | (define-funs-rec
        |   ( (f2 ((x nat)) nat) )
        |   ( (forall ((y nat)) x) ) )
        | (prove  (forall ((y nat)) x) )
        | (assert (forall ((y nat)) x) )
      """.stripMargin)
    )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   x )
        | (define-funs-rec
        |   ( (f2 ((x nat)) nat) )
        |   ( x ) )
        | (prove  x )
        | (assert x )
      """.stripMargin)
    )
    eliminateRedundantQuantifiers.transform(originalProblem) must_==
      expectedProblem
  }

  "unnecessary variables should be removed" in {
    "existential quantifier" in {
      "not all variables are unnecessary" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (exists ((x nat) (y nat) (z nat)) y) )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (exists ((y nat)) y) )
          """.stripMargin)
        )
        eliminateRedundantQuantifiers.transform(originalProblem) must_==
          expectedProblem
      }
      "quantifier should be discarded if it binds no variables" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (exists ((y nat)) x) )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   x )
          """.stripMargin)
        )
        eliminateRedundantQuantifiers.transform(originalProblem) must_==
          expectedProblem
      }
    }
    "universal quantifier" in {
      "not all variables are unnecessary" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (forall ((x nat) (y nat) (z nat)) y) )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (forall ((y nat)) y) )
          """.stripMargin)
        )
        eliminateRedundantQuantifiers.transform(originalProblem) must_==
          expectedProblem
      }
      "quantifier should be discarded if it binds no variables" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   (forall ((y nat)) x) )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            | (define-fun
            |   f1
            |   ((x nat))
            |   nat
            |   x )
          """.stripMargin)
        )
        eliminateRedundantQuantifiers.transform(originalProblem) must_==
          expectedProblem
      }
    }
  }
}
