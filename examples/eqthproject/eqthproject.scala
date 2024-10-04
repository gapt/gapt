package gapt.examples.eqthproject

import gapt.expr._
import gapt.expr.subst.FOLSubstitution
import gapt.examples.Script
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.expr.formula.hol.{instantiate, universalClosure}
import gapt.formats.lean._
import gapt.proofs._
import gapt.proofs.resolution._
import gapt.provers.prover9._

import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.util.parsing.combinator._
import scala.util.Random

import java.io.{File, PrintWriter}

object largeScale {
  // FIXME: don't hardcode this
  // path to the file of all equations (without leading block comment)
  val path_alleq =
    "/home/stefan/Uni/Software/gapt-devel/equational_theories/AllEquations.nocomments.lean"

  /**
   * check (try to prove) the implicaton from => to 
   *
   * Note that this should not be called repeatedly since it imports
   * the list of all equations at each call.
   **/
  def checkImplication(from: Int, to: Int): Option[String] = {
    val equations = tools.EquationImporter(largeScale.path_alleq)
    tools.getLeanProof(equations, from, to)
  }

  /**
   * check all implications in a given list
   * @param fn filename of list of implications
   * @param outfn output file name
   * @param logfn log file name
   **/
  def checkImplicationsFromFile(fn: String, outfn: String, logfn: String) = {
    val impl = tools.PowerfulThmImporter(fn)
    checkImplications(impl, outfn, logfn)
  }

  /**
   * check some randomly chosen entries from a list of implications (useful for debugging)
   * @param fn filename of list of implications
   * @param n number of implications to pick randomly
   * @param outfn output file name
   * @param logfn log file name
   **/
  def checkRandomImplicationsFromFile(fn: String, n: Int, outfn: String, logfn: String) = {
    val rand = new scala.util.Random
    val all_impl = tools.PowerfulThmImporter(fn)

    val buf = ArrayBuffer[(Int, Int)]()
    for (i <- 0 until n)
      buf += all_impl(rand.nextInt(n))
    val impl = buf.toArray

    checkImplications(impl, outfn, logfn)
  }

  /**
   * check implications
   * @param implications the implications to check (given by pairs of equation indices)
   * @param outfn output file name
   * @param logfn log file name
   **/
  def checkImplications(implications: Array[(Int, Int)], outfn: String, logfn: String) = {
    val equations = tools.EquationImporter(path_alleq)

    val writer = new PrintWriter(new File(outfn))
    writer.write("import equational_theories.Magma\n")
    writer.write("import equational_theories.AllEquations\n")
    writer.write("import Mathlib.Tactic\n\n")

    val logWriter = new PrintWriter(new File(logfn))
    var successes = 0
    var noproofs = 0
    var exceptions = 0

    for (i <- 0 until implications.length) {
      val from = implications(i)(0)
      val to = implications(i)(1)

      logWriter.write("(" + (i + 1) + "/" + implications.length + ") checking implication: " + from + " => " + to + "... ")
      try {
        val res = tools.getLeanProof(equations, from, to)
        res match {
          case Some(s) => {
            writer.write(s + "\n")
            logWriter.write("Lean proof exported.\n")
            successes += 1
          }
          case None => {
            logWriter.write("no proof found.\n")
            noproofs += 1
          }
        }
      } catch {
        case _: Throwable => {
          exceptions += 1
          logWriter.write("exception.\n")
        }
      }

      writer.flush()
      logWriter.flush()
    }

    writer.close()

    logWriter.write("\nlean proofs exported: " + successes + "\n")
    logWriter.write("      no proof found: " + noproofs + "\n")
    logWriter.write("          exceptions: " + exceptions + "\n")
    logWriter.close()
  }
}

object tools {

  /**
   * Run prover9 on: EqList[from] implies EqList[to], return a Lean proof
   **/
  def getLeanProof(EqList: Array[FOLAtom], from: Int, to: Int): Option[String] = {
    val f_from = universalClosure(EqList(from))
    val f_to = universalClosure(EqList(to))
    val goal = Sequent(List(f_from), List(f_to))

    val (iGoal, constants) = instGoal(goal)
    Prover9((_ => Seq("assign(max_seconds, 5)"))).getResolutionProof(iGoal) match {
      case Some(p) => {
        val q = simplifyResolutionProof(p)
        val r = LeanExporter.moveParamodsLeft(q)

        val substMap = Map(
          FOLVar("x") -> FOLConst("a"),
          FOLVar("y") -> FOLConst("b"),
          FOLVar("z") -> FOLConst("c"),
          FOLVar("w") -> FOLConst("d"),
          FOLVar("u") -> FOLConst("e"),
          FOLVar("v") -> FOLConst("f")
        )
        val subst = FOLSubstitution(substMap)
        val s = TermReplacement.undoGrounding(r, subst)

        val thmname = "Equation" + from + "_implies_Equation" + to

        Some("@[equational_result]\n" +
          "theorem " + thmname + " (G: Type*) [Magma G] (h: Equation"
          + from + " G): Equation" + to + " G :=\n"
          + LeanExporter(s, LeanExporter.formulaPrinting.none))
      }
      case None => None
    }
  }

  /**
   * Run prover9 on: EqList[from] implies EqList[to], return a Lean proof via LK
   **/
  def getLeanProofViaLK(EqList: Array[FOLAtom], from: Int, to: Int): Option[String] = {
    val f_from = universalClosure(EqList(from))
    val f_to = universalClosure(EqList(to))
    val goal = Sequent(List(f_from), List(f_to))

    val (iGoal, constants) = instGoal(goal)
    Prover9((_ => Seq("assign(max_seconds, 5)"))).getLKProof(iGoal) match {
      case Some(p) => {
        val thmname = "Equation" + from + "_implies_Equation" + to

        Some("theorem " + thmname + " (G: Type*) [Magma G] (h0: Equation"
          + from + " G): Equation" + to + " G := by\n"
          + "  unfold Equation" + from + " at h0\n"
          + "  unfold Equation" + to + "\n"
          + "  intro " + getConstantNames(constants) + "\n"
          + LeanExporter(p))
      }
      case None => None
    }
  }

  def instGoal(goal: HOLSequent): (HOLSequent, List[FOLTerm]) = {
    val nvars = goal(Suc(0)) match {
      case All.Block(xs, _) => xs.length
    }

    val constants = getConstants(nvars)
    val instSuc = instantiate(goal(Suc(0)), constants)
    val instGoal = goal.updated(Suc(0), instSuc)

    (instGoal, constants)
  }

  private def getConstants(n: Int): List[FOLTerm] = { // FIXME
    val a = FOLConst("a")
    val b = FOLConst("b")
    val c = FOLConst("c")
    val d = FOLConst("d")
    val e = FOLConst("e")
    val f = FOLConst("f")

    List(a, b, c, d, e, f).take(n)
  }

  private def getConstantNames(L: List[FOLTerm]): String = { // FIXME
    L.mkString(" ")
  }

  class LeanEqParser extends JavaTokenParsers {
    def line: Parser[FOLAtom] = opt("--") ~ "equation" ~ wholeNumber ~ ":=" ~ eq ^^ { case o ~ l ~ n ~ ":=" ~ e => e }
    def eq: Parser[FOLAtom] = term ~ "=" ~ term ^^ { case t1 ~ "=" ~ t2 => FOLAtom("=", List(t1, t2)) }
    def term: Parser[FOLTerm] = factor ~ "◇" ~ factor ^^ { case f1 ~ "◇" ~ f2 => FOLFunction("f", List(f1, f2)) }
      | factor ^^ { case f => f }
    def factor: Parser[FOLTerm] = "x" ^^ { case s => FOLVar(s) }
      | "y" ^^ { case s => FOLVar(s) }
      | "z" ^^ { case s => FOLVar(s) }
      | "u" ^^ { case s => FOLVar(s) }
      | "v" ^^ { case s => FOLVar(s) }
      | "w" ^^ { case s => FOLVar(s) }
      | "(" ~ term ~ ")" ^^ { case "(" ~ t ~ ")" => t }
  }

  object EquationImporter extends LeanEqParser {
    /* expects filename of list of equations, return list in gapt format */
    def apply(fn: String): Array[FOLAtom] = {
      val buf = ArrayBuffer[FOLAtom]()
      // add dummy equation at position 0 so that array indices match equation numbers
      buf += FOLAtom("=", List(FOLVar("x"), FOLVar("x")))

      for (l <- Source.fromFile(fn).getLines())
        buf += parseAll(line, l).get

      buf.toArray
    }
  }

  class ImplParser extends JavaTokenParsers {
    def line: Parser[(Int, Int)] =
      "Equation" ~ wholeNumber ~ "=>" ~ "Equation" ~ wholeNumber ^^ { case "Equation" ~ from ~ "=>" ~ "Equation" ~ to => (from.toInt, to.toInt) }
  }

  object ImplImporter extends ImplParser {
    def apply(fn: String): Array[(Int, Int)] = {
      val buf = ArrayBuffer[(Int, Int)]()

      for (l <- Source.fromFile(fn).getLines())
        buf += parseAll(line, l).get

      buf.toArray
    }
  }

  class PowerfulThmParser extends JavaTokenParsers {
    def line: Parser[(Int, Int)] =
      wholeNumber ~ wholeNumber ~ wholeNumber ^^ { case from ~ to ~ weight => (from.toInt, to.toInt) }
  }

  object PowerfulThmImporter extends PowerfulThmParser {
    def apply(fn: String): Array[(Int, Int)] = {
      val buf = ArrayBuffer[(Int, Int)]()

      for (l <- Source.fromFile(fn).getLines())
        buf += parseAll(line, l).get

      buf.toArray
    }
  }
}
