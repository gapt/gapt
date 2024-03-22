package gapt.examples
import gapt.expr._
import gapt.expr.ty.Ti
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.epsilon.epsilonize
import gapt.provers.escargot.Escargot

object epsilon extends Script {
  implicit val ctx: MutableContext = MutableContext.default()
  ctx += hoc"ε{?a} : (?a>o)>?a"
  ctx += Ti
  ctx += hoc"P: i>i>i>o"
  ctx += hoc"rat: i>o"; ctx += hoc"pow: i>i>i"
  ctx += hoc"'*': i>i>i"; ctx += hoc"s2: i"; ctx += hoc"2: i"
  ctx += Notation.Infix( "*", Precedence.timesDiv )

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
  val Some( irratProof ) = Escargot getEpsilonProof irratProblem: @unchecked
  println( irratProof )

  require( Escargot.isValid( irratProof.deep ) )
}