package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.proofs.epsilon2.{ EpsilonProof, epsilonize }
import at.logic.gapt.provers.escargot.Escargot

object epsilon extends Script {
  println( "Exercises for the lecture on epsilon calculus at the TU Wien:\n" )

  def printAbbrs()( implicit ctx: Context ) = {
    println( "Abbreviations:" )
    for ( ( c, Abs.Block( vs, eps ) ) <- ctx.get[SkolemFunctions].epsilonDefinitions )
      println( s"  ${c( vs ) === eps}" )
  }

  {
    val threeExists = hof"∃x∃y∃z P(x,y,z)"
    implicit val ctx = MutableContext.guess( threeExists: Expr )
    println( s"Translate $threeExists to a formula in epsilon calculus:" )
    println( epsilonize( threeExists ) )
    printAbbrs()
    println()
  }

  println( "Prove using epsilon calculus: there exist irrational numbers x and y such that x^y is rational:\n" )
  val irratProblem =
    hof"""¬rat(s2) ∧ rat(2) ∧ s2*s2 = 2 ∧ pow(s2,2) = 2 ∧
          ∀x∀y∀z (pow (pow x y) z = pow x (y*z)) ⊃
          ∃x∃y (¬rat(x) ∧ ¬rat(y) ∧ rat(pow x y))"""
  println( s"Formalization: $irratProblem\n" )
  implicit val ctx = MutableContext.guess( irratProblem: Expr )
  println( s"Epsilonization:\n${epsilonize( irratProblem )}" )
  printAbbrs()
  println( "Proof:" )
  val Some( irratProof ) = Escargot getEpsilonProof irratProblem
  println( irratProof )

  require( Escargot isValid irratProof.deep )
}