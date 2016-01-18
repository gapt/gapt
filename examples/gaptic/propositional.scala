import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{parseFormula, parseTerm}
import at.logic.gapt.proofs.gaptic.tactics._

val A = FOLAtom("A")
val B = FOLAtom("B")

val lemma = new Lemma(
	Sequent(Seq("initAnt" -> Imp(A, B)), Seq("initSuc" -> Or(And(A,B), Neg(A))))
) {
	use(orR("initSuc"))
	use(negR("initSuc_2"))
	use(andR("initSuc_1"))
	use(axiomLog)
	use(impL("initAnt"))
	use(axiomLog)
	use(axiomLog)
} qed

val lemma2 = new Lemma(
	Sequent(Seq("initAnt" -> Imp(A, B)), Seq("initSuc" -> Or(And(A,B), Neg(A))))
) {
	use(orR("initSuc"))
	use(negR("initSuc_2"))
	use(andR("initSuc_1"))
	use(axiom)
	use(impL)
	use(axiom)
	use(axiom)
} qed

val cutTest = new Lemma(
	Sequent(Seq("a1" -> And(A,B), "a2" -> Imp(B,A)), Seq("s1" -> Or(B,A), "s2" -> Neg(And(B,A))))
) {
	use(cut(Imp(FOLAtom("C"), Bottom()), "cfm"))
}

val direct = new Lemma(
	Sequent(Seq("A" -> A, "B" -> B), Seq("B" -> B))
) {
	use(axiom)
} qed

val lemmaProp = new Lemma(
	Sequent(Seq("a" -> Imp(A, B)), Seq("s" -> Or(And(A,B), Neg(A))))
) {
	use(impL)
	use(prop)
	use(prop)
} qed