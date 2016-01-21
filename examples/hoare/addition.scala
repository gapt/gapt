package at.logic.gapt.examples.hoare

import at.logic.gapt.examples.Script
import at.logic.gapt.expr.Neg
import at.logic.gapt.formats.hoare.ProgramParser
import at.logic.gapt.proofs.expansion.extractInstances
import at.logic.gapt.proofs.hoare.{ ForLoop, SimpleLoopProblem }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9

object addition extends Script {
  val p = ProgramParser.parseProgram( "for y < z do x := s(x) od" )
  val A = parseFormula( "x = k" )
  val B = parseFormula( "x = k + z" )
  val g_p0 = parseFormula( "(all x (x + 0 = x))" )
  val g_ps = parseFormula( "(all x (all y (s(x+y) = x + s(y))))" )
  val g = List( g_p0, g_ps )

  val f = parseFormula( "k + y = x" )

  val slp = SimpleLoopProblem( p.asInstanceOf[ForLoop], g, A, B )

  val nLine = sys.props( "line.separator" )

  println( slp.loop.body )
  println( slp.programVariables )
  println( slp.pi )

  val instanceSeq = slp.instanceSequent( 2 )
  println( instanceSeq )
  val proof = Prover9.getLKProof( instanceSeq ).get

  println( nLine + "Expansion sequent:" )
  val expansionSequent = LKToExpansionProof( proof ).expansionSequent
  extractInstances( expansionSequent ) foreach println

  println( nLine + "Deep sequent:" )
  val deepSequent = expansionSequent map {
    _.deep
  }
  deepSequent.antecedent.foreach( println( _ ) )
  deepSequent.succedent.foreach( f => println( Neg( f ) ) )

}
