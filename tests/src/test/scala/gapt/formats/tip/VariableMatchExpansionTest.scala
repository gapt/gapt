package gapt.formats.tip

import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.expandVariableMatchExpressions
import org.specs2.mutable.Specification

class VariableMatchExpansionTest extends Specification {

  "variable match-expressions should be expanded in all expressions" in {

    val input =
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x (case Z Z) (case (S y) x) )))
        | (define-funs-rec
        |   (
        |     (f2 ((x nat)) nat)
        |   )
        |   (
        |     (forall ((x nat)) (match x (case Z Z) (case (S y) x) ))
        |   ))
        | (prove (forall ((x nat)) (match x (case Z Z) (case (S y) x) )))
        | (assert (forall ((x nat)) (match x (case Z Z) (case (S y) x) )))
      """.stripMargin

    val originalProblem = TipSmtParser.parse( input )
    val transformedProblem =
      expandVariableMatchExpressions.transform( originalProblem )

    transformedProblem.definitions( 0 ) must_== originalProblem.definitions( 0 )
    transformedProblem.definitions( 1 ) must
      beAnInstanceOf[TipSmtFunctionDefinition]
    transformedProblem.definitions( 1 ) must_!= originalProblem.definitions( 1 )
    transformedProblem.definitions( 2 ) must
      beAnInstanceOf[TipSmtMutualRecursiveFunctionDefinition]
    transformedProblem.definitions( 2 ) must_!= originalProblem.definitions( 2 )
    transformedProblem.definitions( 3 ) must
      beAnInstanceOf[TipSmtGoal]
    transformedProblem.definitions( 3 ) must_!= originalProblem.definitions( 3 )
    transformedProblem.definitions( 4 ) must
      beAnInstanceOf[TipSmtAssertion]
    transformedProblem.definitions( 4 ) must_!= originalProblem.definitions( 4 )
  }

  "unquantified variables should not be expanded" in {
    val input =
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match y (case Z Z) (case (S y) x) )))
      """.stripMargin
    val originalProblem = TipSmtParser.parse( input )
    val transformedProblem =
      expandVariableMatchExpressions.transform( originalProblem )
    transformedProblem.definitions( 1 ) must_== originalProblem.definitions( 1 )
  }

  "existential variable should be expanded properly" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (exists ((x nat)) (match x (case Z Z) (case (S y) x) )))
      """.stripMargin )
    val expectedProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (exists ((x nat)) (or Z (exists ((y nat)) (S y))) ))
      """.stripMargin )
    expandVariableMatchExpressions.transform( originalProblem ) must_==
      expectedProblem
  }

  "universal variable should be expanded properly" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x (case Z Z) (case (S y) x) )))
      """.stripMargin )
    val expectedProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (and Z (forall ((y nat)) (S y))) ))
      """.stripMargin )
    expandVariableMatchExpressions.transform( originalProblem ) must_==
      expectedProblem
  }

  "variable capture should be avoided" in {
    val originalProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall
        |     ((x nat))
        |     (match x
        |       (case Z Z)
        |       (case (S y) (forall ((y Nat)) (= y x) ) ) )))
      """.stripMargin )
    val expectedProblem = TipSmtParser.parse(
      """
        | (declare-datatypes () ( (nat (Z) (S (p nat)))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall
        |     ((x nat))
        |     (and
        |       Z
        |       (forall ((y nat)) (forall ((y_0 Nat)) (= y_0 (S y)) )  ))  ))
      """.stripMargin )
    expandVariableMatchExpressions.transform( originalProblem ) must_==
      expectedProblem
  }
}
