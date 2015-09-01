import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.{parse, time}

import at.logic.gapt.examples.{UniformAssociativity3ExampleProof, SumExampleProof, LinearEqExampleProof}
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{FOLSubTerms, Numeral, FOLSubstitution, Utils}
import at.logic.gapt.expr.hol.{univclosure, toNNF, simplify, lcomp}
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansionTrees.{removeFromExpansionSequent, ExpansionSequent, InstanceTermEncoding}
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.provers.inductionProver.{SipProver, SimpleInductionProof}
import at.logic.gapt.provers.maxsat.QMaxSAT
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import org.apache.log4j.{Logger, Level}

for (c <- Seq(minimizeSipGrammar.getClass, minimizeRecursionScheme.getClass))
  Logger.getLogger(c.getName).setLevel(Level.DEBUG)

if (false) {

  //val terms = TermsExtraction(SumExampleProof(7)).set
  val N = 8
  val terms = (0 until N) map { i =>
    FOLFunction("r", Utils.numeral(i), Utils.numeral(N - i))
  }

  val nfs = normalForms(FOLSubTerms(terms), Seq(FOLVar("x"), FOLVar("y")))

  val nfRecSchem = RecursionScheme(
    (for (arg1 <- nfs; arg2 <- nfs; if freeVariables(Seq(arg1, arg2)).isEmpty)
      yield Rule(FOLFunction("A"), FOLFunction("B", arg1, arg2))).toSet ++
      (for (nf <- nfs; if !nf.isInstanceOf[FOLVar]) yield Rule(FOLFunction("B", FOLVar("x"), FOLVar("y")), nf))
  )

  val targets = terms.map(FOLFunction("A") -> _)
  println(lcomp(simplify(toNNF((new RecSchemGenLangFormula(nfRecSchem))(targets)))))

  val nfG = normalFormsProofVectGrammar(terms, Seq(2))
  println(lcomp(simplify(toNNF(new VectGrammarMinimizationFormula(nfG).coversLanguage(terms)))))

  val minimized = time {
    minimizeRecursionScheme(nfRecSchem, targets)
  }
  println(minimized)

  val minG = time {
    minimizeVectGrammar(nfG, terms, new QMaxSAT)
  }
  println(minG)

}

if (true) {
//  val endSequent = FSequent(
//    Seq("P(0,x)", "P(x,f(y)) & P(x,g(y)) -> P(s(x),y)", "P(x,y) -> Q(x)")
//      map (s => univclosure(parseFormula(s))),
//    Seq(FOLAtom("Q", SimpleInductionProof.alpha)))
//  val endSequent = FSequent(
//    Seq("s(x+y) = x+s(y)", "s(x+y) = s(x)+y", "x+0 = x", "0+x = x")
//      map (s => univclosure(parseFormula(s))),
//    Seq(Eq(
//      FOLFunction("+", FOLConst("k"), SimpleInductionProof.alpha),
//      FOLFunction("+", SimpleInductionProof.alpha, FOLConst("k")))))
//  val endSequent = FSequent(
//    Seq(
//      "f(0) = 1",
//      "s(x)*f(x) = f(s(x))",
//      "g(x,0) = x",
//      "g(x*s(y),y) = g(x,s(y))",
//      "x*1 = x",
//      "1*x = x",
//      "(x*y)*z = x*(y*z)")
//      map (s => univclosure(parseFormula(s))),
//    Seq(Eq(
//      FOLFunction("g", FOLConst("1"), SimpleInductionProof.alpha),
//      FOLFunction("f", SimpleInductionProof.alpha))))
//  val instanceProofs = (0 until 5) map { n =>
//    val instanceSequent = FOLSubstitution( SimpleInductionProof.alpha -> Utils.numeral( n ) )( endSequent )
//    println( s"[n=$n] Proving $instanceSequent" )
//    n -> new Prover9Prover().getExpansionSequent( instanceSequent ).get
//  }

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

    val eqaxioms = Sequent( R::S::T::Tprime::CSuc::CPlus::CPlusL::CgR::CMultR::Nil, Nil )

    removeFromExpansionSequent( eseq, eqaxioms )
  }
  val endSequent = Sequent(
    Seq("s(x+y) = x+s(y)", "x+0 = x")
      map (s => univclosure(parseFormula(s))),
    Seq(parseFormula("(x+x)+x = x+(x+x)")))
  val instanceProofs =
      (0 until 6).map { n => n -> removeEqAxioms(LKToExpansionProof(UniformAssociativity3ExampleProof(n))) }

  val termEncoding = InstanceTermEncoding( endSequent )
  var instanceLanguages = instanceProofs map {
    case ( n, expSeq ) =>
      n -> termEncoding.encode( expSeq )
  }

  // Ground the instance languages.
  instanceLanguages = instanceLanguages map {
    case ( n, lang ) =>
      val groundingSubst = FOLSubstitution( freeVariables( lang ).
        map { c => FOLVar( c.name ) -> FOLConst( c.name ) }.toSeq )
      n -> lang.map( groundingSubst.apply )
  }

  val nfRecSchem = SipRecSchem.normalForms(instanceLanguages)
  println(nfRecSchem.rules.size)
  val minimized = time{minimizeRecursionScheme(nfRecSchem, SipRecSchem.toTargets(instanceLanguages), SipRecSchem.targetFilter, new QMaxSAT)}
  println(minimized);println

  (0 until 10) foreach { i =>
    val instanceLang = minimized.language(FOLFunction(SipRecSchem.A, Numeral(i))) filter {
      case FOLFunction("A" | "G", _) => false
      case _ => true
    }
    val instanceSeq = FOLSubstitution(FOLVar("x") -> Numeral(i))(termEncoding.decodeToFSequent(instanceLang))
    val isCovered = instanceLanguages.find(_._1 == i).map(_._2.toSet subsetOf instanceLang)
    val isTaut = new VeriTProver().isValid(instanceSeq)
    println(s"$i: tautology=$isTaut covers=$isCovered")
  }

  val sipG = SipRecSchem.toSipGrammar(minimized)
  println(sipG)

  val nfSipG = normalFormsSipGrammar(instanceLanguages)
  println(nfSipG.productions.size)
  println(time{minimizeSipGrammar(nfSipG, instanceLanguages, new QMaxSAT)})
}