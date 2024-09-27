package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.toOuterConditionalNormalForm
import org.specs2.mutable.Specification

class ToOuterConditionalNormalFormTest extends Specification {
  "transformation should be applied to all expressions" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile("""
        | (define-fun f1 ((x nat)) nat
        |   (and
        |     (ite a b c) d
        |   )
        | )
        | (define-funs-rec
        |   (
        |     (f3 ((x nat)) nat)
        |   )
        |   (
        |     (and
        |       (ite a b c) d
        |     )
        |   )
        | )
        | (prove
        |   (and
        |     (ite a b c) d
        |   )
        | )
        | (assert
        |   (and
        |     (ite a b c) d
        |   )
        | )
        | (assert-not
        |   (and
        |     (ite a b c) d
        |   )
        | )
      """.stripMargin)
    )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile("""
        | (define-fun f1 ((x nat)) nat
        |   (ite a
        |     (and b d)
        |     (and c d)
        |   )
        | )
        | (define-funs-rec
        |   (
        |     (f3 ((x nat)) nat)
        |   )
        |   (
        |     (ite a
        |       (and b d)
        |       (and c d)
        |     )
        |   )
        | )
        | (prove
        |   (ite a
        |     (and b d)
        |     (and c d)
        |   )
        | )
        | (assert
        |   (ite a
        |     (and b d)
        |     (and c d)
        |   )
        | )
        | (assert-not
        |   (ite a
        |     (and b d)
        |     (and c d)
        |   )
        | )
      """.stripMargin)
    )
    toOuterConditionalNormalForm.transform(originalProblem) must_==
      expectedProblem
  }

  "and" in {
    "ite should permute over and" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (and
          |     (ite a b c) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (and b d)
          |     (and c d)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over and" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (and
          |     (match a ( ( Z b) ( (S y) (c y)) ) ) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (and b d))
          |     ( (S y) (and (c y) d)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (and
          |     (or (ite a b c) d) e
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (and (or b d) e)
          |     (and (or c d) e)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
            | (define-fun f1 ((y nat)) nat
            |   (and
            |     (match a (( Z b) ( (S y) (c y) )) ) y
            |   )
            | )
          """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
            | (define-fun f1 ((y nat)) nat
            |   (match a
            |     (( Z (and b y))
            |     ( (S y_0) (and (c y_0) y)))
            |   )
            | )
          """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "or" in {
    "ite should permute over or" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (or
          |     (ite a b c) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (or b d)
          |     (or c d)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over eq" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (or
          |     (match a (( Z b) ( (S y) (c y) )) ) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (or b d))
          |     ( (S y) (or (c y) d)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (or
          |     (and (ite a b c) d) e
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (or (and b d) e)
          |     (or (and c d) e)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (or
          |     (match a (( Z b) ( (S y) (c y) )) ) y
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (match a
          |     (( Z (or b y))
          |     ( (S y_0) (or (c y_0) y)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "eq" in {
    "ite should permute over eq" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (eq
          |     (ite a b c) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (eq b d)
          |     (eq c d)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over eq" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (eq
          |     (match a (( Z b) ( (S y) (c y) ) )) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (eq b d))
          |     ( (S y) (eq (c y) d)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (eq
          |     (or (ite a b c) d) e
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (eq (or b d) e)
          |     (eq (or c d) e)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (eq
          |     (match a (( Z b) ( (S y) (c y) ) ) ) y
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (match a
          |     (( Z (eq b y))
          |     ( (S y_0) (eq (c y_0) y)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "not" in {
    "ite should permute over not" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (not
          |     (ite a b c)
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (not b)
          |     (not c)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over not" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (not
          |     (match a (( Z b) ( (S y) (c y) ) ) )
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (not b))
          |     ( (S y) (not (c y))))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (not
          |     (or (ite a b c) d)
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (not (or b d))
          |     (not (or c d))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "forall" in {
    "ite should not permute over forall" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (forall ((y bool))
          |     (ite y b c)
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (forall ((y bool))
          |     (ite y b c)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
            | (define-fun f1 ((x nat)) nat
            |   (forall ((y bool))
            |     (or (ite y b c) d)
            |   )
            | )
          """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
            | (define-fun f1 ((x nat)) nat
            |   (forall ((y bool))
            |     (ite y
            |       (or b d)
            |       (or c d)
            |     )
            |   )
            | )
          """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "exists" in {
    "ite should not permute over exists" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (exists ((y bool))
          |     (ite y b c)
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (exists ((y bool))
          |     (ite y b c)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (exists ((y bool))
          |     (or (ite y b c) d)
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (exists ((y bool))
          |     (ite y
          |       (or b d)
          |       (or c d)
          |     )
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "ite" in {
    "condition should be flattened (ite)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite (ite a b c) d e)
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a (ite b d e) (ite c d e))
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "condition should be flattened (match)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite (match a (( Z b) ( (S y) (c y)))) d e)
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a (( Z (ite b d e)) ( (S y) (ite (c y) d e))))
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "condition flattening should avoid variable capture (1)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite (match a (( Z b) ( (S y) (c y)))) y e)
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a (( Z (ite b y e)) ( (S y_0) (ite (c y_0) y e))))
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "condition flattening should avoid variable capture (2)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite (match a (( Z b) ( (S y) (c y)))) d y)
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a (( Z (ite b d y)) ( (S y_0) (ite (c y_0) d y))))
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a (and (ite b c d) e) f)
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a (ite b (and c e) (and d e)) f)
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "match" in {
    "matched expression should be flattened (ite)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match (ite a b c) (( Z d) ( (S y) (e y))))
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (match b (( Z d) ( (S y) (e y) )))
          |     (match c (( Z d) ( (S y) (e y) )))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "matched expression should be flattened (match)" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match
          |     (match a (( Z b) ( (S y) (c y) )))
          |     (( Z2 d)
          |     ( (S2 z) (e z)))
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z     (match b     (( Z2 d) ( (S2 z) (e z) ))))
          |     ( (S y) (match (c y) (( Z2 d) ( (S2 z) (e z) )))))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a (( Z (or (ite y b c) d)) ( (S y) (e y))))
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a (( Z (ite y (or b d) (or c d))) ( (S y) (e y))))
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "condition flattening should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match
          |     (match a (( Z b) ( (S y) (c y) )))
          |     (( Z2 d)
          |     ( (S2 z) (e z y)))
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z
          |     (match b
          |       (( Z2 d) ( (S2 z) (e z y) )))
          |     )
          |     ( (S y_0)
          |       (match (c y_0) (( Z2 d) ( (S2 z) (e z y))))
          |     ))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "imp" in {
    "ite should permute over imp" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (=>
          |     (ite a b c) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (=> b d)
          |     (=> c d)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over imp" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (=>
          |     (match a (( Z b) ( (S y) (c y) ) ) ) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (=> b d))
          |     ( (S y) (=> (c y) d)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (=>
          |     (or (ite a b c) d) e
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (=> (or b d) e)
          |     (=> (or c d) e)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (=>
          |     (match a (( Z b) ( (S y) (c y) ) ) ) y
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (match a
          |     (( Z (=> b y))
          |     ( (S y_0) (=> (c y_0) y)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }

  "fun" in {
    "ite should permute over fun" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (f2
          |     (ite a b c) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (f2 b d)
          |     (f2 c d)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "match should permute over fun" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (f2
          |     (match a (( Z b) ( (S y) (c y) ) ) ) d
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (match a
          |     (( Z (f2 b d))
          |     ( (S y) (f2 (c y) d)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should apply to subexpressions" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (f2
          |     (or (ite a b c) d) e
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((x nat)) nat
          |   (ite a
          |     (f2 (or b d) e)
          |     (f2 (or c d) e)
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
    "transformation should avoid variable capture" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (f2
          |     (match a (( Z b) ( (S y) (c y) ) ) ) y
          |   )
          | )
        """.stripMargin)
      )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile("""
          | (define-fun f1 ((y nat)) nat
          |   (match a
          |     (( Z (f2 b y))
          |     ( (S y_0) (f2 (c y_0) y)))
          |   )
          | )
        """.stripMargin)
      )
      toOuterConditionalNormalForm.transform(originalProblem) must_==
        expectedProblem
    }
  }
}
