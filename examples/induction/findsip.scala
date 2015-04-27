import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.{extractExpansionSequent, time, parse}
import at.logic.gapt.examples.UniformAssociativity3ExampleProof
import at.logic.gapt.language.fol.{toNNF, removeTopAndBottom, lcomp}
import at.logic.gapt.proofs.expansionTrees.{removeFromExpansionSequent, ExpansionSequent}
import at.logic.gapt.proofs.lk.algorithms.cutIntroduction._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.provers.maxsat.QMaxSAT
import at.logic.gapt.provers.sat4j.Sat4j

def removeEqAxioms( eseq: ExpansionSequent ) = {
  // removes all equality axioms that appear in examples/ProofSequences.scala
  val R = parse.fol( "Forall x =(x,x)" )
  val S = parse.fol( "Forall x Forall y Imp =(x,y) =(y,x)" )
  val T = parse.fol( "Forall x Forall y Forall z Imp And =(x,y) =(y,z) =(x,z)" )
  val Tprime = parse.fol( "Forall x Forall y Forall z Imp =(x,y) Imp =(y,z) =(x,z)" )
  val CSuc = parse.fol( "Forall x Forall y Imp =(x,y) =(s(x),s(y))" )
  val CPlus = parse.fol( "Forall x Forall y Forall u Forall v Imp =(x,y) Imp =(u,v) =(+(x,u),+(y,v))" )
  val CPlusL = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(+(y,x),+(z,x))" ) // congruence plus left
  val CgR = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(g(x,y),g(x,z))" ) // congruence of g on the right
  val CMultR = parse.fol( "Forall x Forall y Forall z Imp =(x,y) =(*(z,x),*(z,y))" ) // congruence of mult right

  val eqaxioms = new FSequent( R::S::T::Tprime::CSuc::CPlus::CPlusL::CgR::CMultR::Nil, Nil )

  removeFromExpansionSequent( eseq, eqaxioms )
}

val N = 5
val instanceLanguages = ((1 until N) map { n =>
  println(s"Proving for n=$n")
  val instanceProof = UniformAssociativity3ExampleProof(n)
//  val instanceProof = LinearEqExampleProof(n)
//  val instanceProof = FactorialFunctionEqualityExampleProof(n)
  val instanceLanguage = TermsExtraction(removeEqAxioms(extractExpansionSequent(instanceProof))).set
  println(s"Instance sequent: ${instanceProof.root}")
  println(s"Instance language:"); instanceLanguage foreach println; println
  n -> instanceLanguage
}) :+ (0 -> Seq(parse.p9term("tuple2(0)"))) // FIXME: fix associativity proof to do n=0 as well

println(s"Covering grammar consisting of all normal forms:")
val nfGrammar = time { normalFormsSipGrammar(instanceLanguages) }
//nfGrammar.productions foreach println; println
println(s"${nfGrammar.productions.size} productions.")

val logicalComp = lcomp(removeTopAndBottom(toNNF(SipGrammarMinimizationFormula(nfGrammar).coversLanguageFamily(instanceLanguages))))
println(s"Logical complexity of the minimization formula: $logicalComp")

println(s"Minimized grammar:")
val minGrammar = time { minimizeSipGrammar(nfGrammar, instanceLanguages, maxSATSolver = new QMaxSAT()) }
minGrammar.productions foreach println; println

instanceLanguages foreach { case (n, instanceLanguage) =>
  println(s"Checking covering for n=$n: ")
  val instanceGrammar = minGrammar.instanceGrammar(n)
//  println("Instance language:"); instanceLanguage foreach println
//  println("Instance grammar:"); instanceGrammar.productions foreach println
  println("Is it covered? " + new Sat4j().solve(new GrammarMinimizationFormula(instanceGrammar).coversLanguage(instanceLanguage)).isDefined)
  println
}
