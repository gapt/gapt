package gapt.examples.eqthproject

import gapt.expr._
import gapt.examples.Script
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.expr.formula.hol.instantiate
import gapt.proofs._
import gapt.provers.prover9._
import gapt.formats.lean._

import scala.util.parsing.combinator._

object example extends Script {
  val Equation38 = fof"!x!y f(x,x)=f(x,y)"
  val Equation42 = fof"!x!y!z f(x,y)=f(x,z)"
  val g = Sequent(List(Equation38), List(Equation42))
  println(tools.getLeanProof(g))
}

object tools {
  /*
   * Produces Lean code to prove goal by calling prover9. Expects goal to contain two
   * universally quantified equations, one in the antecedens and one in the consequent.
   **/
  def getLeanProof(goal: HOLSequent): String = {
    println("(DEBUG eqthproj) calling prover9")

    val ( iGoal, constants )= instGoal( goal )
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

  def instGoal( goal: HOLSequent ) : ( HOLSequent, List[FOLTerm] ) = {
    val nvars = goal(Suc(0)) match {
      case All.Block(xs, _) => xs.length
    }

    val constants = getConstants(nvars)
    println("(DEBUG eqthproj) constants: " + constants)

    val instSuc = instantiate(goal(Suc(0)), constants)
    val instGoal = goal.updated(Suc(0), instSuc)

    println("(DEBUG eqthproj) goal: " + goal)
    println("(DEBUG eqthproj) instGoal: " + instGoal)

    ( instGoal, constants )
  }

  private def getConstants(n: Int): List[FOLTerm] = {
    var rv = List[FOLTerm]()
    for (i <- 0 until n) rv = rv :+ FOLConst("a" + (i + 1))
    rv
  }

  private def getConstantNames( L: List[FOLTerm] ): String = {
    var rv = L(0).toString
    for (i <- 1 until L.length) rv += " " + L(i).toString
    rv
  }

  class LeanEqParser extends JavaTokenParsers {
    def eq: Parser[Any] = term~"="~term
    def term: Parser[Any] = factor~rep("∘"~factor)
    def factor: Parser[Any] = "x" | "y" | "z" | "u" | "v" | "w" | "("~term~")"
  }

  object Importer extends LeanEqParser {
    def apply( s:String ) = {
      println( parseAll( eq, s ))
    }
  }
}
