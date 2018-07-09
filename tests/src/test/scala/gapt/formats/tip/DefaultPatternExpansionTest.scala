package gapt.formats.tip

import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.expandDefaultPatterns
import org.specs2.mutable.Specification

class DefaultPatternExpansionTest extends Specification {

  "default cases should be expanded everywhere" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x (case Z Z) (case default x) )))
        | (define-funs-rec
        |   (
        |     (f2 ((x nat)) nat)
        |   )
        |   (
        |     (forall ((x nat)) (match x (case Z Z) (case default x) ))
        |   ))
        | (prove (forall ((x nat)) (match x (case Z Z) (case default x) )))
        | (assert (forall ((x nat)) (match x (case Z Z) (case default x) )))
      """.stripMargin )
    val expectedProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x (case Z Z) (case (S x_0) x) )))
        | (define-funs-rec
        |   (
        |     (f2 ((x nat)) nat)
        |   )
        |   (
        |     (forall ((x nat)) (match x (case Z Z) (case (S x_0) x) ))
        |   ))
        | (prove (forall ((x nat)) (match x (case Z Z) (case (S x_0) x) )))
        | (assert (forall ((x nat)) (match x (case Z Z) (case (S x_0) x) )))
      """.stripMargin )
    expandDefaultPatterns.transform( originalProblem ) must_== expectedProblem
  }

  "default case should be replaced by missing constructors" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (it (Z) (S1 (p nat)) (S2 (p nat)) )))
        | (define-fun
        |   f1 ((x it)) it
        |   (forall ((x it)) (match x
        |   (case (S1 x_0) x) (case default x) )))
      """.stripMargin )
    val expectedProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (it (Z) (S1 (p nat)) (S2 (p nat)) )))
        | (define-fun
        |   f1 ((x it)) it
        |   (forall ((x it)) (match x
        |   (case (S1 x_0) x) (case Z x) (case (S2 x_0) x) )))
      """.stripMargin )
    expandDefaultPatterns.transform( originalProblem ) must_== expectedProblem
  }

  "default case expansion should avoid variable capture" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (it (Z) (S1 (p nat)) (S2 (p nat)) )))
        | (define-fun
        |   f1 ((x_0 it)) it
        |   (forall ((x_0 it)) (match x_0
        |   (case (S1 x_1) x_0) (case default x_0) )))
      """.stripMargin )
    val TipSmtFunctionDefinition( _, _, _, _,
      TipSmtForall(
        _,
        TipSmtMatch(
          _,
          Seq(
            _,
            _,
            TipSmtCase(
              TipSmtConstructorPattern(
                _,
                Seq( TipSmtIdentifier( name ) ) ), _ ) ) ) ) ) =
      expandDefaultPatterns.transform( originalProblem ).definitions( 1 )

    name must_!= "x_0"
  }
}