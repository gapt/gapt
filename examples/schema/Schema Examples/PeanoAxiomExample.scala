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

object PeanoAxiomExample extends TacticsProof {
 // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat", hoc"p : nat > nat")
  ctx += Sort("i")
  // Term Constants
  //ctx += hoc"z:i"
  
  //Predicate Constants
  ctx += hoc"E: nat>nat>o"
  //ctx += hoc"LEQ: i>i>o"
  //ctx += hoc"LE: i>i>o"

   // Proof symbols
  ctx += hoc"delta: nat>nat"
  ctx += hoc"pi: nat>i>i>nat"

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
  //ctx += "A2" -> hos" (s(p)= s(q) ) :- (p = q) "  
  ctx += "A3" -> hos" :- (p+0) = p"
  ctx += "A4" -> hos" :-  = p+s(q) = s(p+q)  " // check: maybe mehr Klammern
  //ctx += "A5" -> hos" :- (p*0) = 0 " // check: maybe mehr Klammern
  //ctx += "A6" -> hos" :- (p*s(q)) = ((p*q)+p) " // check: maybe mehr Klmmern
 /* ctx += "A7" -> hos" :- s(p) = (p+1) " */

 // ctx += "Eq1" -> hos""
  ctx += "Eq2" -> hos":- s=s"
  ctx += "Additional" -> hos"p = q :- s(p) = s(q)" // Replace this by schema proof

  // Helper
  // End Sequent
  //val esPi = Sequent(Seq(hof" n = m "), Seq( hof" s(n) = s(m) "))
  // Proof Declaration
  //ctx += ProofNameDeclaration(le"Pi m", esDelta)


  // Proof of 0 is a left identity
  // End Sequents
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
     cut("cut1", hof" s(0+m) = 0+s(m)  ") 

     forget("Suc_0")
     theory

     eql("cut1", "Suc_0")
     forget("cut1")

     cut("cut2", hof"0+m=m")

     forget("Suc_0")
     ref("delta")

     theory //helper
     //unfold("+") atMost 1 in "Suc_0"
     //axiomRefl
  }
  ctx += ProofDefinitionDeclaration(le"delta (s m)", deltaSc)
  // Instantiation
  val deltaThree = instantiateProof(le"delta (s (s (s 0)))")
  // prooftool(FirstSchema.phiThree)


  

}