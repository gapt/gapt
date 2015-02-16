import at.logic.calculi.expansionTrees.MWeakQuantifier
import at.logic.cli.GAPScalaInteractiveShellLibrary._
import at.logic.language.hol.Neg
import at.logic.language.hoare.{ForLoop, SimpleLoopProblem}

val p = parse.program("for y < z do x := set(x, s(y), get(x, y)) od")
val f = parse.p9("k <= z -> get(x,k) = get(x,o)")
val g_s = parse.p9("(all x (s(x) != o))")
val g_lr = parse.p9("(all x (x <= x))")
val g_0l = parse.p9("(all x (o <= x))")
val g_l0 = parse.p9("(all x (x <= o -> o = x))") // order of equality is important...
val g_sl = parse.p9("(all x (all y (x <= y -> x <= s(y))))")
val g_ls = parse.p9("(all x (all y (x <= s(y) -> x <= y | s(y) = x)))")
val g_ge = parse.p9("(all x (all y (all z (get(set(x,y,z),y) = z))))")
val g_gn = parse.p9("(all x (all y (all z (all w (w != y -> get(set(x,y,z),w) = get(x,w))))))")
val g = List(g_s, g_lr, g_0l, g_l0, g_sl, g_ls, g_ge, g_gn)

val slp = new SimpleLoopProblem(p.asInstanceOf[ForLoop], g, parse.fol("T()"), f)

println(slp.loop.body)
println(slp.programVariables)
println(slp.pi(0))

val instanceSeq = slp.instanceSequent(1)
println(instanceSeq)
val proof = prover9.getProof(instanceSeq).get

val expansionSequent = compressExpansionSequent(extractExpansionSequent(proof))
expansionSequent.antecedent.foreach {
  case MWeakQuantifier(formula, instances) =>
    println(s"$formula:")
    instances.foreach { case (inst, terms) => println(s"  $terms ($inst)") }
  case _ => Nil
}
val deepSequent = expansionSequent.toDeep
deepSequent.antecedent.foreach(println(_))
deepSequent.succedent.foreach(f => println(Neg(f)))

