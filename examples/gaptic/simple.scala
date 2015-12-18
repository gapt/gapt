import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{parseFormula, parseTerm}
import at.logic.gapt.proofs.gaptic.tactics._

/* Test: Or right */
val A = FOLAtom("A")
val B = FOLAtom("B")

val hs = OpenAssumption(Sequent(Seq(), Seq("init" -> Or(A,B))))
val ps = new ProofState(hs)
val Some(ps2) = OrRightTactic()(ps)

/* Test: Imp right, forall left, exists right */
val pstGoal = OpenAssumption(Sequent(Seq(), Seq("init" -> Imp(All(FOLVar("x"), FOLAtom( "A", FOLVar("x") )), Ex(FOLVar("x"), FOLAtom( "A", FOLVar("x") ))))))
val pstState = new ProofState(pstGoal)
val Some(pstState2) = ImpRightTactic()(pstState)
val Some(pstState3) = ForallLeftTactic(FOLConst( "t" ), "instanceAll")(pstState2)
val Some(pstState4) = ExistsRightTactic(FOLConst( "t" ), "instanceEx")(pstState3)

/* Test: Lemma */
val lemma = new Lemma(
	Sequent(Seq("initAnt" -> Imp(A, B)), Seq("initSuc" -> Or(And(A,B), Neg(A))))
) {
	use(OrRightTactic("initSuc"))
	use(NegRightTactic("initSuc_2"))
	use(AndRightTactic("initSuc_1"))
	use(LogicalAxiomTactic(A))
	use(ImpLeftTactic("initAnt"))
	use(LogicalAxiomTactic(A))
	use(LogicalAxiomTactic(B))
} qed

/* Drinker test */
val drinker = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x all y (P(x) -> P(y)))" )))) {
	use(ExistsRightTactic( parseTerm( "c" ), "D1" ))
	use(ForallRightTactic( FOLVar( "x_0" ), "D1" ))
	use(ExistsRightTactic( FOLVar( "x_0" ), "D2" ))
	use(ForallRightTactic( FOLVar( "x_1" ), "D2" ))
	use(ImpRightTactic())
	use(ImpRightTactic())
	use(LogicalAxiomTactic(FOLAtom("P", FOLVar("x_0"))))
} qed

/* Eigen variable test */
val evtest = new Lemma( Sequent( Seq( "F1" -> parseFormula( "(exists x P(x))" )), Seq( "F2" -> parseFormula( "(exists x P(x))" )))) {
	use(ExistsLeftTactic( FOLVar("z") ))
}

val dualdrinker = new Lemma( Sequent( Seq( "D" -> parseFormula( "(all x exists y (P(x) & -P(y)))")), Nil )) {
	use(ForallLeftTactic( parseTerm( "c" ), "D1" ))
	use(ExistsLeftTactic( FOLVar( "y" ) ))
	use(ForallLeftTactic( parseTerm( "y" ), "D2" ))
	use(ExistsLeftTactic( FOLVar( "y0" )))
	use(AndLeftTactic( "D2" ))
}