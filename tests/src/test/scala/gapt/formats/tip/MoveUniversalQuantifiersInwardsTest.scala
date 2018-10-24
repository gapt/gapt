package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.moveUniversalQuantifiersInwards
import org.specs2.mutable.Specification

class MoveUniversalQuantifiersInwardsTest extends Specification {

  "transformation should apply to function definitions" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat (forall ((x nat)) (and a b) ) )
        | (define-funs-rec
        |   ( (f3 ((x nat)) nat))
        |   ( (forall ((x nat)) (and a b) ) ) )
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   ( and
        |     (forall ((x nat)) a )
        |     (forall ((x nat)) b ) ) )
        | (define-funs-rec
        |   ( (f3 ((x nat)) nat))
        |   ( (and (forall ((x nat)) a)  (forall ((x nat)) b)) ) )
      """.stripMargin ) )
    moveUniversalQuantifiersInwards.transform( originalProblem ) must_==
      expectedProblem
  }

  "universal quantifier should be distributed over conjuncts" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat (forall ((x nat)) (and a b) ) )
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   ( and
        |     (forall ((x nat)) a )
        |     (forall ((x nat)) b ) ) )
      """.stripMargin ) )
    moveUniversalQuantifiersInwards.transform( originalProblem ) must_==
      expectedProblem
  }

  "universal quantifiers should be moved inwards in ite-expressions" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   (ite
        |     (forall ((x nat)) (and a b) )
        |     (forall ((x nat)) (and a b) )
        |     (forall ((x nat)) (and a b) )
        |   )
        | )
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   (ite
        |     (forall ((x nat)) (and a b) )
        |     ( and
        |       (forall ((x nat)) a )
        |       (forall ((x nat)) b )
        |     )
        |     ( and
        |       (forall ((x nat)) a )
        |       (forall ((x nat)) b )
        |     )
        |   )
        | )
      """.stripMargin ) )
    moveUniversalQuantifiersInwards.transform( originalProblem ) must_==
      expectedProblem
  }

  "universal quantifiers should be moved inwards inside conjunction" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   (and (forall ((x nat)) (and a b) ) c ) )
      """.stripMargin ) )
    val expectedProblem = TipSmtParser.parse(
      StringInputFile( """
        | (define-fun f1 ((x nat)) nat
        |   (and ( and
        |     (forall ((x nat)) a )
        |     (forall ((x nat)) b ) ) c ) )
      """.stripMargin ) )
    moveUniversalQuantifiersInwards.transform( originalProblem ) must_==
      expectedProblem
  }
}
