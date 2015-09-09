import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary._
import at.logic.gapt.expr.Neg
import at.logic.gapt.proofs.expansionTrees.METWeakQuantifier
import at.logic.gapt.proofs.hoare.{ForLoop, SimpleLoopProblem}
import at.logic.gapt.proofs.lk.LKToExpansionProof

val p = parse.program("for y < z do x := s(x) od")
val A = parse.p9("x = k")
val B = parse.p9("x = k + z")
val g_p0 = parse.p9("(all x (x + 0 = x))")
val g_ps = parse.p9("(all x (all y (s(x+y) = x + s(y))))")
val g = List(g_p0, g_ps)

val f = parse.p9("k + y = x")

val slp = SimpleLoopProblem(p.asInstanceOf[ForLoop], g, A, B)

val nLine = sys.props("line.separator")

println(slp.loop.body)
println(slp.programVariables)
println(slp.pi)

val instanceSeq = slp.instanceSequent(2)
println(instanceSeq)
val proof = prover9.getProof(instanceSeq).get

println( nLine + "Expansion sequent:")
val expansionSequent = compressExpansionSequent(LKToExpansionProof(proof))
expansionSequent.antecedent.foreach {
  case METWeakQuantifier(formula, instances) =>
    println(s"$formula:")
    instances.foreach { case (inst, terms) => println(s"  $terms ($inst)") }
  case _ => Nil
}

println( nLine + "Deep sequent:")
val deepSequent = expansionSequent.toDeep
deepSequent.antecedent.foreach(println(_))
deepSequent.succedent.foreach(f => println(Neg(f)))

