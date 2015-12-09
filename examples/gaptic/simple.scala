import at.logic.gapt.proofs.gaptic._

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
	use(ImpLeftTactic("initAnt"))
	use(LogicalAxiomTactic(A))
	use(LogicalAxiomTactic(A))
	use(ImpLeftTactic("initAnt"))
	use(LogicalAxiomTactic(A))
	use(LogicalAxiomTactic(B))
} qed