package gapt.formats.tip

import gapt.formats.StringInputFile
import gapt.formats.tip.parser.TipSmtParser
import gapt.formats.tip.transformation.useDefiningFormulas
import org.specs2.mutable.Specification

class UseDefiningFormulasTest extends Specification {

  "all function definitions should be transformed" in {
    val originalProblem = TipSmtParser.parse(
      StringInputFile( """
        | (declare-datatypes ((nat 0)) ( ( (Z) (S (p nat)))))
        | (define-fun f1 ((x nat)) nat a)
        | (define-fun f2 ((x nat)) nat b)
        | (define-funs-rec
        |   ( (f3 ((x nat)) nat) (f4 ((x nat)) nat) )
        |   ( c d ) )
      """.stripMargin ) )
    val transformedProblem = useDefiningFormulas.transform( originalProblem )
    transformedProblem.definitions( 1 ) must_!= originalProblem.definitions( 1 )
    transformedProblem.definitions( 2 ) must_!= originalProblem.definitions( 2 )
    transformedProblem.definitions( 3 ) must_!= originalProblem.definitions( 3 )
  }

  "function definitions should be transformed properly" in {
    "parameterless function" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-fun f1 () nat a)
        """.stripMargin ) )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-fun f1 () nat (= (f1) a))
        """.stripMargin ) )
      useDefiningFormulas.transform( originalProblem ) must_== expectedProblem
    }

    "function has at least one parameter" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-fun f1 ( (x nat) ) nat a)
        """.stripMargin ) )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-fun f1 ((x nat)) nat (forall ((x nat)) (= (f1 x) a)) )
        """.stripMargin ) )
      useDefiningFormulas.transform( originalProblem ) must_== expectedProblem
    }
  }

  "mutually recursive function definitions should be transformed" in {
    "all definitions should be transformed" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-funs-rec
          |   ( (f3 ((x nat)) nat) (f4 ((y nat)) nat) )
          |   ( c d ) )
        """.stripMargin ) )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-funs-rec
          |   ( (f3 ((x nat)) nat) (f4 ((y nat)) nat) )
          |   ( (forall ((x nat)) (= (f3 x) c))
          |     (forall ((y nat)) (= (f4 y) d)) ) )
        """.stripMargin ) )
      useDefiningFormulas.transform( originalProblem ) must_== expectedProblem
    }
    "no empty quantifier should be introduced" in {
      val originalProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-funs-rec
          |   ( (f3 () nat) )
          |   ( c ) )
        """.stripMargin ) )
      val expectedProblem = TipSmtParser.parse(
        StringInputFile( """
          | (define-funs-rec
          |   ( (f3 () nat) )
          |   ( (= (f3) c)) )
        """.stripMargin ) )
      useDefiningFormulas.transform( originalProblem ) must_== expectedProblem
    }
  }
}
