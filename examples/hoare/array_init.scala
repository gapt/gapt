import at.logic.cli.GAPScalaInteractiveShellLibrary._
import at.logic.language.hoare.{ForLoop, SimpleLoopProblem}

val p = parse.program("for y < z do x := set(x, s(y), get(x, y)) od")
val f = parse.fol("Imp Leq(k, z) =(get(x,k), get(x,o))")
val g_s = parse.fol("Forall x Neg =(s(x), o)")
val g_lr = parse.fol("Forall x Leq(x,x)")
val g_0l = parse.fol("Forall x Leq(o,x)")
val g_l0 = parse.fol("Forall x Imp Leq(x,o) =(o,x)") // order of equality is important...
val g_sl = parse.fol("Forall x Forall y Imp Leq(x,y) Leq(x,s(y))")
val g_ls = parse.fol("Forall x Forall y Imp Leq(x,s(y)) Or Leq(x,y) =(s(y),x)")
val g_ge = parse.fol("Forall x Forall y Forall z =(get(set(x,y,z),y), z)")
val g_gn = parse.fol("Forall x Forall y Forall z Forall w Imp Neg =(w,y) =(get(set(x,y,z),w), get(x,w))")
val g = List(g_s, g_lr, g_0l, g_l0, g_sl, g_ls, g_ge, g_gn)

val slp = new SimpleLoopProblem(p.asInstanceOf[ForLoop], g, parse.fol("T()"), f)

println(slp.loop.body)
println(slp.programVariables)
println(slp.pi(0))

println(slp.instanceSequent(2))

val proof = prover9.getProof(slp.instanceSequent(1)).get
println(proof)

val expansionSequent = extractExpansionSequent(proof)
println(expansionSequent)
