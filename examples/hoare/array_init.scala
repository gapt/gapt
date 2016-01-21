package at.logic.gapt.examples.hoare

import at.logic.gapt.examples.Script
import at.logic.gapt.expr.{ FOLAtom, Neg }
import at.logic.gapt.formats.hoare.ProgramParser
import at.logic.gapt.proofs.expansion.extractInstances
import at.logic.gapt.proofs.hoare.{ ForLoop, SimpleLoopProblem }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9

object array_init extends Script {
  val p = ProgramParser.parseProgram( "for y < z do x := set(x, s(y), get(x, y)) od" )
  val f = parseFormula( "k <= z -> get(x,k) = get(x,0)" )
  val g_s = parseFormula( "(all x (s(x) != 0))" )
  val g_lr = parseFormula( "(all x (x <= x))" )
  val g_0l = parseFormula( "(all x (0 <= x))" )
  val g_l0 = parseFormula( "(all x (x <= 0 -> 0 = x))" )
  // order of equality is important...
  val g_sl = parseFormula( "(all x (all y (x <= y -> x <= s(y))))" )
  val g_ls = parseFormula( "(all x (all y (x <= s(y) -> x <= y | s(y) = x)))" )
  val g_ge = parseFormula( "(all x (all y (all z (get(set(x,y,z),y) = z))))" )
  val g_gn = parseFormula( "(all x (all y (all z (all w (w != y -> get(set(x,y,z),w) = get(x,w))))))" )
  val g = List( g_s, g_lr, g_0l, g_l0, g_sl, g_ls, g_ge, g_gn )

  val slp = SimpleLoopProblem( p.asInstanceOf[ForLoop], g, FOLAtom( "T" ), f )

  println( slp.loop.body )
  println( slp.programVariables )
  println( slp.pi )

  val instanceSeq = slp.instanceSequent( 1 )
  println( instanceSeq )
  val proof = Prover9.getLKProof( instanceSeq ).get

  val expansionSequent = LKToExpansionProof( proof ).expansionSequent
  extractInstances( expansionSequent ) foreach println

  val deepSequent = expansionSequent map { _.deep }
  deepSequent.antecedent.foreach( println( _ ) )
  deepSequent.succedent.foreach( f => println( Neg( f ) ) )
}
