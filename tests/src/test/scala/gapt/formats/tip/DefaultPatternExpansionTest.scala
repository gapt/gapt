package gapt.formats.tip

import gapt.formats.StringInputFile
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

  "default cases should be expanded in matched expressions" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
                         | (declare-datatype nat ((Z) (S (p nat))))
                         | (prove (forall ((x nat)) (match (match x ((_ x))) ((Z Z) ( _ x)))))
                       """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
                         | (declare-datatype nat ( (Z) (S (p nat))))
                         | (prove (forall ((x nat)) (match ( match x ((Z x) ( (S x_0) x ) ) ) (( Z Z) ( (S x_0) x) ))))
                       """.stripMargin ) )
    expandDefaultPatterns.transform( originalProblem ) must_== expectedProblem
  }

  "default cases should be expanded everywhere" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatype nat ((Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x ((Z Z) (_ x)))))
        | (define-funs-rec
        |   (
        |     (f2 ((x nat)) nat)
        |   )
        |   (
        |     (forall ((x nat)) (match x ((Z Z) (_ x))))
        |   ))
        | (prove (forall ((x nat)) (match x ((Z Z) ( _ x)))))
        | (assert (forall ((x nat)) (match x (( Z Z) ( _ x)))))
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatype nat ( (Z) (S (p nat))))
        | (define-fun
        |   f1
        |   ((x nat))
        |   nat
        |   (forall ((x nat)) (match x (( Z Z) ( (S x_0) x)))))
        | (define-funs-rec
        |   (
        |     (f2 ((x nat)) nat)
        |   )
        |   (
        |     (forall ((x nat)) (match x (( Z Z) ( (S x_0) x) )))
        |   ))
        | (prove (forall ((x nat)) (match x (( Z Z) ( (S x_0) x) ))))
        | (assert (forall ((x nat)) (match x (( Z Z) ( (S x_0) x) ))))
      """.stripMargin ) )
    expandDefaultPatterns.transform( originalProblem ) must_== expectedProblem
  }

  "default case should be replaced by missing constructors" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatype it ((Z) (S1 (p nat)) (S2 (p nat))))
        | (define-fun
        |   f1 ((x it)) it
        |   (forall ((x it)) (match x
        |   (( (S1 x_0) x) ( _ x)))))
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatype it ((Z) (S1 (p nat)) (S2 (p nat))))
        | (define-fun
        |   f1 ((x it)) it
        |   (forall ((x it)) (match x
        |   (( (S1 x_0) x) ( Z x) ( (S2 x_0) x)))))
      """.stripMargin ) )
    expandDefaultPatterns.transform( originalProblem ) must_== expectedProblem
  }

  "default case expansion should avoid variable capture" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatype it ((Z) (S1 (p nat)) (S2 (p nat))))
        | (define-fun
        |   f1 ((x_0 it)) it
        |   (forall ((x_0 it)) (match x_0
        |   (( (S1 x_1) x_0) ( _ x_0) ))))
      """.stripMargin ) )
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