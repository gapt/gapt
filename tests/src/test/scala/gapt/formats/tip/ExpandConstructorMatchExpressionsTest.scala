package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.expandConstructorMatchExpressions
import org.specs2.mutable.Specification

class expandConstructorMatchExpressionsTest extends Specification {

  "constructor match-expressions should be expanded everywhere" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   ( match Z (( Z a) ( (S y) b)) )
        | )
        | (define-funs-rec
        |   (
        |     (f3 ((x nat)) nat)
        |   )
        |   (
        |     ( match Z ( ( Z a) ( (S y)  b)  ) )
        |   )
        | )
        | (prove
        |   ( match Z (( Z a) ( (S y) b)) )
        | )
        | (assert
        |   ( match Z (( Z a) ( (S y) b)))
        | )
        | (assert-not
        |   ( match Z (( Z a) ( (S y) b)) )
        | )
      """.stripMargin)
    )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   a )
        | (define-funs-rec
        |   (  (f3 ((x nat)) nat)  )
        |   ( a )
        | )
        | (prove a )
        | (assert a )
        | (assert-not a )
      """.stripMargin)
    )
    expandConstructorMatchExpressions.transform(originalProblem) must_==
      expectedProblem
  }

  "constructor match-expressions should expand properly" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p1 nat) (p2 nat) (p3 nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   ( match (S a1 a2 a3)
        |     (( Z a)
        |     ( (S x1 x2 x3) (f1 (S x1 x2 x3)) ))
        |   )
        | )
      """.stripMargin)
    )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p1 nat) (p2 nat) (p3 nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   (f1 (S a1 a2 a3))
        | )
      """.stripMargin)
    )
    expandConstructorMatchExpressions.transform(originalProblem) must_==
      expectedProblem
  }

  "constructor match-expression should expand from outside to inside" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   ( match (S (S a))
        |     (( Z b)
        |     ( (S x1)
        |       ( match x1
        |         (( Z c)
        |         ( (S x2) x2)))
        |       )
        |     )
        |   )
        | )
      """.stripMargin)
    )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile("""
        | (declare-datatype nat ((Z) (S (p nat))))
        |
        | (define-fun f1 ((x nat)) nat
        |   a
        | )
      """.stripMargin)
    )
    expandConstructorMatchExpressions.transform(originalProblem) must_==
      expectedProblem
  }

  "constructor match-expressions should be expanded in subexpressions" in {
    "and" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (and
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     ) b
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (and true b )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "or" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (or
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     ) b
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (or true b )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "imp" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (imp
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     ) b
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (imp true b )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "eq" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (eq
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     ) b
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (eq true b )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "forall" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (forall ((z nat))
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     )
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (forall ((z nat)) true)
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "exists" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (exists ((z nat))
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     )
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (exists ((z nat)) true)
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "match" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (match x
          |     ((  Z Z )
          |     (  (S z)
          |       ( match (S (S a))
          |         (( Z b)
          |         ( (S x1) true))
          |       ))
          |     )
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (match x
          |     ((  Z Z )
          |     (  (S z) true ))
          |   )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
    "ite" in {
      "expand in condition" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite
            |     ( match (S (S a))
            |       (( Z b)
            |       ( (S x1) true))
            |     ) b c
            |   )
            | )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite true b c)
            | )
          """.stripMargin)
        )
        expandConstructorMatchExpressions.transform(originalProblem) must_==
          expectedProblem
      }
      "expand in ifTrue" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite
            |     b
            |     ( match (S (S a))
            |       (( Z b)
            |       ( (S x1) true))
            |     )
            |     c
            |   )
            | )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite b true c)
            | )
          """.stripMargin)
        )
        expandConstructorMatchExpressions.transform(originalProblem) must_==
          expectedProblem
      }
      "expand in ifFalse" in {
        val originalProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite
            |     b
            |     c
            |     ( match (S (S a))
            |       (( Z b)
            |       ( (S x1) true))
            |     )
            |   )
            | )
          """.stripMargin)
        )
        val expectedProblem = TipSmtParser.parse(
          StringInputFile("""
            | (declare-datatype nat ((Z) (S (p nat))))
            |
            | (define-fun f1 ((x nat)) bool
            |   (ite b c true)
            | )
          """.stripMargin)
        )
        expandConstructorMatchExpressions.transform(originalProblem) must_==
          expectedProblem
      }
    }
    "func" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (f1
          |     ( match (S (S a))
          |       (( Z b)
          |       ( (S x1) true))
          |     ) b
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (declare-datatype nat ((Z) (S (p nat))))
          |
          | (define-fun f1 ((x nat)) bool
          |   (f1 true b )
          | )
        """.stripMargin)
      )
      expandConstructorMatchExpressions.transform(originalProblem) must_==
        expectedProblem
    }
  }
}
