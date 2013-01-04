package at.logic.provers.prover9

/**
 * Tests for the LADR language parser
 */

import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.base.Clause
import _root_.at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import _root_.at.logic.provers.atp.commands.base.{SetStreamCommand, PrependCommand}
import _root_.at.logic.provers.atp.commands.sequents.SetTargetClause
import _root_.at.logic.provers.atp.Prover
import at.logic.calculi.lk.base.FSequent
import at.logic.provers.prover9.commands.{Prover9TermParser, Prover9InitCommand}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mock.Mockito
import org.mockito.Matchers._
import java.io.IOException
import at.logic.calculi.resolution.robinson.{Formatter, RobinsonResolutionProof}

import at.logic.calculi.occurrences.factory
import at.logic.parsing.language.tptp.TPTPFOLExporter
import util.parsing.input.Position

// to use matchers like anyInt()
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base.types.FSequent
import java.io.File.separator

@RunWith(classOf[JUnitRunner])
class Prover9ParserTest extends SpecificationWithJUnit {
  "The Prover9 language parser" should {
    "handle conjunctions and atoms" in {
      //skipped("not working yet")
      val cases = List(
        "p(X)","A","-p(y)","-p(Y)",
        "P(X)","a","-P(y)","-P(Y)",
        "P(x) & P(b)", "q(x) &q(x) & p(y)", "A&B", "X&Y&Z",
        "(P(x) & P(b))", "(q(x) &q(x) & p(y))", "(A&B)", "(X&Y&Z)",
        "q(x) &(q(x) & p(y))", "(X&Y)&Z"
     )

      var good : List[FOLFormula] = List[FOLFormula]()
      var bad  : List[(String, Position)] = List[(String, Position)]()
      for (s <- cases) {
        Prover9TermParser.parseAll(Prover9TermParser.formula, s) match {
          case Prover9TermParser.Success(result, _) =>
            println(result)
            good = result :: good
          case Prover9TermParser.Failure(msg, input) =>
            //s must beEqualTo("Failure:"+input.pos.toString + ": " +  msg)
            println("Failure!")
            bad = (msg,input.pos) :: bad
          case Prover9TermParser.Error(msg, input) =>
            //s must beEqualTo("Error:"+input.pos.toString + ": " +  msg)
            println("Error!")
            bad = (msg,input.pos) :: bad

        }
      }
      println("===============")
      bad map println
      bad must beEmpty
    }

    "handle simple formulas" in {
      //skipped("not working yet")
      val cases = List(
        "p(X)","A","-p(y)","-p(Y)",
        "P(X)","a","-P(y)","-P(Y)",
        "P(x) & P(b)", "q(x) &q(x) & p(y)", "A&B", "X&Y&Z",
        "(P(x) & P(b))", "(q(x) &q(x) & p(y))", "(A&B)", "(X&Y&Z)",
        "P(x) | P(b)", "q(x) |q(x) | p(y)", "A|B", "X|Y|Z",
        "(P(x) | P(b))", "(q(x) |q(x) | p(y))", "(A|B)", "(X|Y|Z)",
        "P(x) -> P(b)",  "A->B", // "X->Y->Z", "q(x) ->q(x) -> p(y)",
        "(P(x) -> P(b))", "(A->B)", //"(X->Y->Z)", "(q(x) ->q(x) -> p(y))",
        "P(x) <- P(b)", "A<-B", //"X<-Y<-Z", , "q(x) <-q(x) <- p(y)"
        "(P(x) <- P(b))", "(A<-B)", //"(X<-Y<-Z)", "(q(x) <-q(x) <- p(y))",
        "P(x) <-> P(b)",  "A<->B", //"X<->Y<->Z", "q(x) <->q(x) <-> p(y)",
        "(P(x) <-> P(b))", "(A<->B)", //"(X<->Y<->Z)", "(q(x) <->q(x) <-> p(y))",
        "q(x) &(q(x) & p(y))", "(X&Y)&Z",
        "(all X p(X))","(exists X p(X))"
      )

      cases map ( (s:String) =>
        Prover9TermParser.parseAll(Prover9TermParser.formula, s) match {
          case Prover9TermParser.Success(result, _) =>
            println(result)
            true must beEqualTo(true)
          case Prover9TermParser.NoSuccess(msg, input) =>
            s must beEqualTo(input.pos.toString + ": " +  msg)
        })
    }

    "handle complex formulas" in {
      //skipped("not working yet")
      val cases = List(
        "(all X (P(X) & Q(X)))", "(all X (P(X) & Q(X) & R(X,X)))",
        "(exists X (P(X) & Q(X)))", "(exists X (P(X) & Q(X) & R(X,X)))",
        "(all X (P(X) | Q(X)))", "(all X (P(X) | Q(X) | R(X,X)))",
        "(exists X (P(X) | Q(X)))", "(exists X (P(X) | Q(X) | R(X,X)))"

      )

      cases map ( (s:String) =>
        Prover9TermParser.parseAll(Prover9TermParser.formula, s) match {
          case Prover9TermParser.Success(result, _) =>
            println(result)
            true must beEqualTo(true)
          case Prover9TermParser.NoSuccess(msg, input) =>
            s must beEqualTo(input.pos.toString + ": " +  msg)
        })
    }

    "goat puzzle endsequent" in {
      //skipped("not working yet")
      val oendsequent =
        """p(south,south,south,south,start) &
          | (all T (p(south,north,south,north,T) -> p(north,north,south,north,go_alone(T)))) &
          | (all T1 (p(north,north,south,north,T1) -> p(south,north,south,north,go_alone(T1)))) &
          | (all T2 (p(south,south,north,south,T2) -> p(north,south,north,south,go_alone(T2)))) &
          | (all T3 (p(north,south,north,south,T3) -> p(south,south,north,south,go_alone(T3)))) &
          | (all T4 (p(south,south,south,north,T4) -> p(north,north,south,north,take_wolf(T4)))) &
          | (all T5 (p(north,north,south,north,T5) -> p(south,south,south,north,take_wolf(T5)))) &
          | (all T6 (p(south,south,north,south,T6) -> p(north,north,north,south,take_wolf(T6)))) &
          | (all T7 (p(north,north,north,south,T7) -> p(south,south,north,south,take_wolf(T7)))) &
          | (all X all Y all U (p(south,X,south,Y,U) -> p(north,X,north,Y,take_goat(U)))) &
          | (all X1 all Y1 all V (p(north,X1,north,Y1,V) -> p(south,X1,south,Y1,take_goat(V)))) &
          | (all T8 (p(south,north,south,south,T8) -> p(north,north,south,north,take_cabbage(T8)))) &
          | (all T9 (p(north,north,south,north,T9) -> p(south,north,south,south,take_cabbage(T9)))) &
          | (all U1 (p(south,south,north,south,U1) -> p(north,south,north,north,take_cabbage(U1)))) &
          | (all V1 (p(north,south,north,north,V1) -> p(south,south,north,south,take_cabbage(V1)))) ->
          | (exists Z p(north,north,north,north,Z))""".stripMargin


      Prover9TermParser.parseAll(Prover9TermParser.formula, oendsequent) match {
        case Prover9TermParser.Success(result, _ ) =>
          println(result)
          "success" must beEqualTo("success")
        case Prover9TermParser.NoSuccess(msg, input) =>
          throw new Exception("Could not parse endsequent! "+msg+ " "+input.pos)
      }

    }

  }


}
