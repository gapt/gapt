package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.epsilon.epsilonize
import at.logic.gapt.proofs.reduction.{ HOFunctionReduction, LambdaEliminationReduction }
import at.logic.gapt.provers.escargot.Escargot

object epsilon extends Script {
  println( "Exercises for the lecture on epsilon calculus at the TU Wien:\n" )

  val threeExists = hof"∃x∃y∃z P(x,y,z)"
  println( s"Translate $threeExists to a formula in epsilon calculus:" )
  println( epsilonize( threeExists ) )
  println()

  println( "Prove using epsilon calculus: there exist irrational numbers x and y such that x^y is rational:\n" )
  val irratProblem =
    hof"""¬rat(s2) ∧ rat(2) ∧ s2*s2 = 2 ∧ pow(s2,2) = 2 ∧
          ∀x∀y∀z (pow (pow x y) z = pow x (y*z)) →
          ∃x∃y (¬rat(x) ∧ ¬rat(y) ∧ rat(pow x y))"""
  println( s"Formalization: $irratProblem\n" )
  println( "Proof:" )
  val Some( irratProof ) = Escargot getEpsilonProof irratProblem
  println( irratProof )

  val reduction = LambdaEliminationReduction() |> HOFunctionReduction()
  require( Escargot isValid reduction.forward( irratProof.deep )._1 )
}