package gapt.examples.eqthproject

import gapt.expr._
import gapt.examples.Script
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.expr.formula.hol.{instantiate,universalClosure}
import gapt.proofs._
import gapt.provers.prover9._
import gapt.formats.lean._

import scala.collection.mutable.ArrayBuffer
import scala.io.Source
import scala.util.parsing.combinator._

object example extends Script {
  val Equations = tools.Importer(
    "/home/stefan/Uni/Software/gapt-devel/AllEquations.nocomments.lean" )
  println( tools.getLeanProof( Equations, 2, 5 ))
}

object tools {
  /**
   * Run prover9 on: EqList[from] implies EqList[to], return a Lean proof
   **/
  def getLeanProof( EqList: Array[FOLAtom], from:Int, to:Int ): String = {
    val f_from = universalClosure(EqList(from))
    val f_to = universalClosure(EqList(to))
    val g = Sequent(List(f_from), List(f_to))
    println( "goal is: " + g )
    getLeanProof( g )
  }

  /*
   * Produces Lean code to prove goal by calling prover9. Expects goal to contain two
   * universally quantified equations, one in the antecedens and one in the consequent.
   **/
  def getLeanProof(goal: HOLSequent): String = {
    println("(DEBUG eqthproj) calling prover9")

    val (iGoal, constants) = instGoal(goal)
    Prover9.getLKProof(iGoal) match {
      case Some(p) => {
        println(p)

        "theorem eqimpl (G: Type*) [Magma G] (h0: " + LeanExporter.exportFormulaWithG(goal(Ant(0)))
          + "): ( " + LeanExporter.exportFormulaWithG(goal(Suc(0))) + " ) := by\n"
          + "  intro " + getConstantNames(constants) + "\n"
          + LeanExporter(p)
      }
      case None => "no proof found."
    }
  }

  def instGoal(goal: HOLSequent): (HOLSequent, List[FOLTerm]) = {
    val nvars = goal(Suc(0)) match {
      case All.Block(xs, _) => xs.length
    }

    val constants = getConstants(nvars)
    println("(DEBUG eqthproj) constants: " + constants)

    val instSuc = instantiate(goal(Suc(0)), constants)
    val instGoal = goal.updated(Suc(0), instSuc)

    println("(DEBUG eqthproj) goal: " + goal)
    println("(DEBUG eqthproj) instGoal: " + instGoal)

    (instGoal, constants)
  }

  private def getConstants(n: Int): List[FOLTerm] = {
    var rv = List[FOLTerm]()
    for (i <- 0 until n) rv = rv :+ FOLConst("a" + (i + 1))
    rv
  }

  private def getConstantNames(L: List[FOLTerm]): String = {
    var rv = L(0).toString
    for (i <- 1 until L.length) rv += " " + L(i).toString
    rv
  }

  class LeanEqParser extends JavaTokenParsers {
    def line: Parser[FOLAtom] = opt("--") ~ "equation" ~ wholeNumber ~ ":=" ~ eq ^^
      { case o~l~n~":="~e => e }
    def eq: Parser[FOLAtom] = term ~ "=" ~ term ^^
      { case t1~"="~t2 => FOLAtom( "=", List( t1, t2 )) }
    def term: Parser[FOLTerm] = factor ~ "∘" ~ factor ^^
      { case f1~"∘"~f2 => FOLFunction( "f", List( f1, f2 )) }
      | factor ^^ { case f => f }
    def factor: Parser[FOLTerm] = "x" ^^ { case s => FOLVar( s ) }
      | "y" ^^ { case s => FOLVar( s ) }
      | "z" ^^ { case s => FOLVar( s ) }
      | "u" ^^ { case s => FOLVar( s ) }
      | "v" ^^ { case s => FOLVar( s ) }
      | "w" ^^ { case s => FOLVar( s ) }
      | "(" ~ term ~ ")" ^^ { case "("~t~")" => t }
  }

  object Importer extends LeanEqParser {
    /* expects filename of list of equations, return list in gapt format */
    def apply(fn: String):Array[FOLAtom] = {
      val buf = ArrayBuffer[FOLAtom]()
      // add dummy equation at position 0 so that array indices match equation numbers
      buf += FOLAtom( "=", List( FOLVar("x"), FOLVar("x") ))

      for ( l <- Source.fromFile( fn ).getLines())
        buf += parseAll(line, l).get

      buf.toArray
    }
  }
}
