
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._

object tape extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"P: i>o"
  ctx += hoc"0:i"
  ctx += hoc"s:i>i"
  ctx += hoc"PAND:i>o"
  ctx += hoc"myproof: i>i"
  val es =  Sequent(Seq(hof"!x PAND(s(x)) = (P(s(x)) &  PAND(x))",hof"PAND(0) = P(0)",hof"PAND(n)"),Seq(hof"PAND(n)"))
  ctx += Context.ProofNameDeclaration(le"myproof n", es)
  val esBc =  Sequent(
Seq(
("Ant_0" -> hof"!x PAND(s(x)) = (P(s(x)) &  PAND(x))"),
("Ant_1" -> hof"PAND(0) = P(0)"),
("Ant_2" -> hof"PAND(0)")
),
Seq(
("Suc_0" ->hof"PAND(0)")
))
  val bc = Lemma(esBc) {
    rewrite ltr "Ant_1" in "Suc_0"
    rewrite ltr "Ant_1" in "Ant_2"
    trivial
  }
 ctx += Context.ProofDefinitionDeclaration(le"myproof 0", bc)

val esSc =  Sequent(
Seq(
("Ant_0" -> hof"!x PAND(s(x)) = (P(s(x)) &  PAND(x))"),
("Ant_1" -> hof"PAND(0) = P(0)"),
("Ant_2" -> hof"PAND(s(n))")
),
Seq(
("Suc_0" ->hof"PAND(s(n))")
))
val sc = Lemma(esSc) {
    rewrite ltr "Ant_0" in "Suc_0"
    rewrite ltr "Ant_0" in "Ant_2"
    andL
    andR
    trivial
    forget("Ant_2_0")
    pLink("myproof")
  }
ctx += Context.ProofDefinitionDeclaration(le"myproof (s n)", sc)

}


