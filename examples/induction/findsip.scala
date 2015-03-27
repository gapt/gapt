import at.logic.algorithms.cutIntroduction._
import at.logic.calculi.expansionTrees.{removeFromExpansionSequent, ExpansionSequent}
import at.logic.calculi.lk.base.FSequent
import at.logic.cli.GAPScalaInteractiveShellLibrary.{time, parse, extractExpansionSequent, prooftool}
import at.logic.examples.UniformAssociativity3ExampleProof
import at.logic.language.fol.{toNNF, removeTopAndBottom, lcomp}
import at.logic.provers.sat4j.Sat4j

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

val N = 3
val instanceLanguages = (1 until N) map { n =>
  println(s"Proving associativity for n=$n")
  val instanceProof = UniformAssociativity3ExampleProof(n)
  val instanceLanguage = TermsExtraction(removeEqAxioms(extractExpansionSequent(instanceProof))).set
  println(s"Instance language:"); instanceLanguage foreach println; println
  n -> instanceLanguage
}

println(s"Covering grammar consisting of all normal forms:")
val nfGrammar = time { normalFormsSipGrammar(instanceLanguages) }
nfGrammar.productions foreach println; println

val logicalComp = lcomp(removeTopAndBottom(toNNF(SipGrammarMinimizationFormula(nfGrammar).coversLanguageFamily(instanceLanguages))))
println(s"Logical complexity of the minimization formula: $logicalComp")

println(s"Minimized grammar:")
val minGrammar = time { minimizeSipGrammar(nfGrammar, instanceLanguages) }
minGrammar.productions foreach println; println

instanceLanguages foreach { case (n, instanceLanguage) =>
  println(s"Checking covering for n=$n: ")
  val instanceGrammar = minGrammar.instanceGrammar(n)
  println("Instance language:"); instanceLanguage foreach println
  println("Instance grammar:"); instanceGrammar.productions foreach println
  println("Is it covered? " + new Sat4j().solve(GrammarMinimizationFormula(instanceGrammar, instanceLanguage)).isDefined)
  println
}
