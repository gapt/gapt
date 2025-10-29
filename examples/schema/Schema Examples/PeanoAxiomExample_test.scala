import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
import gapt.formats.babel.{Notation, Precedence}

object PeanoAxiomExample_test extends TacticsProof {
 // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")
  // Term Constants
  //ctx += hoc"z:i"
  //ctx += hoc"g:i>i"
  //ctx += hoc"f:i>nat"
  //ctx += hoc"max:i>i>i"
  //Predicate Constants
  ctx += hoc"E: nat>nat>o"
  //ctx += hoc"LEQ: i>i>o"
  //ctx += hoc"LE: i>i>o"

   // Proof symbols
  ctx += hoc"delta: nat>nat"

  // primRec functions
  ctx += Notation.Infix("+", Precedence.plusMinus)
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)"
  )
  ctx += Notation.Infix("*", Precedence.timesDiv)
  ctx += PrimRecFun(
    hoc"'*': nat>nat>nat",
    "x * 0 = 0",
    "x * s(y) = (x * y) + x"
  )

  // Theory Axioms
  //ctx += "A1" -> hos" :- 0 != s(p) "
  //ctx += "A2" -> hos" :- (s(p)= s(q) ) -> (p = q) "  
  ctx += "A3" -> hos" :- (0+p) = p"
  ctx += "A4" -> hos" :- p+s(q) = s(p+q) " // check: maybe mehr Klammern
  ctx += "A5" -> hos" :- (p*0) = 0 " // check: maybe mehr Klammern
  ctx += "A6" -> hos" :- (p*s(q)) = ((p*q)+p) " // check: maybe mehr Klmmern
 /* ctx += "A7" -> hos" :- s(p) = (p+1) " */
 


  // End Sequents
 // val esDelta = Sequent(Seq(hof"⊥"), Seq( hof" E((0+m) , m) "))
  val esDelta = Sequent(Seq(), Seq( hof" (0+m) = m "))

 // Proof Declaration
  ctx += ProofNameDeclaration(le"delta m", esDelta)

  // Base Case 
  val esDeltaBc = Sequent(Seq(), Seq("Suc_0" -> hof" (0+0) = 0 "))
  val deltaBc = Lemma(esDeltaBc) {
    theory
  }

  // Step Case 
  val esDeltaSc = Sequent(Seq(), Seq("Suc_0" -> hof" (0+s(m)) = s(m)"))
  val deltaSc = Lemma(esDeltaSc) {
    //sorry
    foTheory
  }



}