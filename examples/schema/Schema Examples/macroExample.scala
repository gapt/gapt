import gapt.proofs.gaptic.TacticsProof
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
import gapt.proofs.lk.rules.InitialSequent

object macroExample extends TacticsProof{

  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")

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
  ctx += "A3" -> hos" :- m = (m+0)"
  ctx += "Ass" -> hos" :- m = n"

  // End Sequents
  val esDelta = Sequent(Seq(), Seq("Suc_0" -> hof" (m+0) = n "))
 


  val deltaBc = Lemma(esDelta) {
   cut("cut1", hof"m = n ") 
   theory
  }


}
