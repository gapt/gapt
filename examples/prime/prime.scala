package at.logic.gapt.examples.prime

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }

/**
 * Created by sebastian on 2/25/16.
 */
case class prime( k: Int ) extends TacticsProof {
  implicit var ctx = FiniteContext()

  // Types
  ctx += Context.Sort("i")

  // Constants
  ctx += Const("0", Ti)
  ctx += Const("1", Ti)
  ctx += Const("+", Ti -> (Ti -> Ti))
  ctx += Const("*", Ti -> (Ti -> Ti))
  ctx += Const("<", Ti -> (Ti -> To))
  ctx += Const("=", Ti -> (Ti -> To))

  //Definitions
  ctx += "set_1" -> le" λk λl l = k"
  ctx += "ν" -> le" λk λl λm ∃n m = k + n*l"
  ctx += "DIV" -> le" λl λk ∃m l *m = k"
  ctx += "PRIME" -> le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"
  ctx += "subset" -> le" λX λY ∀n (X(n) -> Y(n))"
  ctx += "empty" -> le" λX ¬∃n X(n)"
  ctx += "compN" -> le" λX λx ¬X(x)"
  ctx += "union" -> le" λX λY λx (X(x) ∨ Y(x))"
  ctx += "O" -> le" λX ∀m (X(m) -> ∃l subset(ν(m, l+1), X))"
  ctx += "C" -> le" λX O(compN(X))"
  ctx += "INF" -> le" λX ∀k ∃l X(k+(l + 1))"

  // Definitions that depend on k
  val p = for (i <- 0 to k)
    yield FOLConst(s"p_$i")

  p foreach {
    ctx += _
  }

  ctx +=("P[0]", le" set_1(p_0)")
  ctx +=("S[0]", le" ν(0, p_0)")

  for (i <- 1 to k) {
    ctx +=(s"P[$i]", le"union(${P(i - 1)}, set_1 (${p(i)}:i))")
    ctx +=(s"S[$i]", le"union(${S(i - 1)}, ν(0, ${p(i)}))")
  }

  ctx +=(s"F[$k]", hof" ∀l (PRIME(l) <-> ${P(k)}(l))")

  // The paper says X = Y <-> X subset Y ∧ Y subset X, but the current proof uses the definition
  // X = Y <-> ∀x (x ∈ X <-> x ∈ Y). Taking the latter for now.
  val extensionality = hof"∀X ∀Y ( (∀x (X(x) <-> Y(x))) -> X = Y )"

  /* -------------
   * | Subproofs |
   * -------------
   */

  // Proof that complement(complement(X)) = X (under extensionality).
  val compCompProof = Lemma(
    ("EXT" -> extensionality) +: Sequent() :+ "comp" -> hof" compN(compN(X)) = X"
  ) {
    chain("EXT")
    forget("EXT")
    allR("comp", fov"x")
    unfold("compN") in "comp"
    prop
  }

  // Proof that if complement{1} is closed, {1} is open (under extensionality).
  val openClosedProof = Lemma(
    ("EXT" -> extensionality) +: ("C" -> hof" C(compN(set_1(1)))") +: Sequent() :+ "O" -> hof"O(set_1(1))"
  ) {
    unfold("C") in "C"
    cut("CF", hof" compN(compN(set_1 1)) = set_1 1")

    //Left subproof of the cut:
    forget("C", "O")
    insert(compCompProof)

    //Right subproof of the cut:
    forget("EXT")
    unfold("C") in "C"
    eqL("CF", "C").fromLeftToRight
    forget("CF")
    repeat(unfold("O", "set_1", "ν", "subset") in("O", "C"))
    trivial
  }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma(
    Sequent() :+ "nonempty" -> hof" ¬empty(set_1(1))"
  ) {
    repeat(unfold("empty", "set_1") in "nonempty")
    decompose
    exR("nonempty", hoc" 1:i")
    trivial
  }

  // Proof that {1} is finite
  val singletonFinite = Lemma(
    ("infinite" -> hof" INF (set_1 1)") +: Sequent()
  ) {
    repeat(unfold("INF", "set_1") in "infinite")
    allL("infinite", hoc"1: i").forget
    exL("infinite")
    axiomTh
  }

  // Proof of INF(S), S subset X :- INF(X).
  // S and X are free.
  val infiniteSubset = Lemma(
    ("subset_inf" -> hof"INF(S)") +: ("subset" -> hof" subset S X") +: Sequent() :+ "set_inf" -> hof"INF(X)"
  ) {
    unfold("INF") in("subset_inf", "set_inf")
    allR("set_inf")
    allL("subset_inf", fov"k").forget
    exL("subset_inf")
    exR("set_inf", fov"l").forget
    unfold("subset") in "subset"
    chain("subset")
    trivial
  }

  // Proof that every nonempty open set is infinite.
  val phi2 = Lemma(
    Sequent() :+ "goal" -> hof"∀X ((O(X) ∧ ¬ empty(X)) -> INF(X))"
  ) {
    decompose
    unfold("empty") in "goal_0_1"
    decompose
    unfold("O") in "goal_0_0"
    decompose
    allL("goal_0_0", fov"n").forget
    impL("goal_0_0")

    trivial // n ∈ X :- n ∈ X -- do we need to expand this further?

    forget("goal_0_1")
    exL("goal_0_0")
    cut("CF", hof"INF(ν(n, l+1))")

    // Left subproof: ν(n, l+1) is infinite
    forget("goal_0_0", "goal_1")
    unfold("INF") in "CF"
    allR("CF")
    exR("CF", fot" n * (l + (1 + 1)) + l * (k+1)").forget
    unfold("ν") in "CF"
    exR("CF", fot"n +(k + 1)").forget
    axiomTh

    // Right subproof:
    insert(infiniteSubset)
  }

  /**
    * Proof of x ∈ S[n] :- ∃y ( y ∈ P[n] ∧ x ∈ ν(0,y) )
    *
    * @param n
    * @return
    */
  def varrho2(n: Int): LKProof = {
    val endSequent = ("Ant" -> hof" ${S(n)}(x)") +: Sequent() :+ ("Suc" -> hof"∃y (${P(n)}(y) ∧ ν 0 y x)")

    n match {
      case 0 =>
        Lemma(endSequent) {
          unfold("S[0]") in "Ant"
          exR(p(0)).forget
          andR

          unfold("P[0]", "set_1") in "Suc"
          trivial

          unfold("ν") in("Ant", "Suc")
          exL
          exR(fov"n").forget
          trivial
        }

      case _ =>
        Lemma(endSequent) {
          unfold(s"S[$n]", "union") in "Ant"
          orL

          cut("CF", hof"∃y (${P(n - 1)}(y) ∧ ν 0 y x)")

          forget("Suc")
          insert(varrho2(n - 1))

          forget("Ant")
          exL
          exR(fov"y").forget
          andR

          unfold(s"P[$n]", "union", "set_1") in "Suc"
          prop

          andL
          unfold("ν") in("CF_1", "Suc")
          exL
          exR("Suc", fov"n").forget
          trivial

          exR(p(n)).forget
          andR

          forget("Ant")
          unfold(s"P[$n]", "union", "set_1") in "Suc"
          orR
          trivial

          unfold("Ant", "ν") in("Ant", "Suc")
          exL
          exR("Suc", fov"n").forget
          trivial
        }

    }

    // Proof of F[k] :- x ∈ S[k] -> x ∈ comp({1})
    val psi1Left: LKProof = {
      val endSequent = ("Ant1" -> F(k).asInstanceOf[HOLFormula]) +: Sequent() :+ ("Suc" -> hof" ${S(k)}(x) -> compN(set_1(1))(x) ")

      Lemma(endSequent) {
        decompose
        unfold("compN") in "Suc_1"
        cut("CF", hof"¬x = 1")

        forget("Suc_1")
        cut("CF2", hof" ∃y (${P(k)}(y) ∧ ν(0,y)(x))")

        forget("Ant1", "CF")
        insert(varrho2(k))

        forget("Suc_0")
        unfold(s"F[$k]") in "Ant1"
        decompose
        allL("Ant1", fov"y")
        decompose
        forget("Ant1_0_0", "Ant1")
        impL

        unfold(s"P[$k]", (k to 0 by -1) map { j => s"P[$j]" }: _*) in("CF2_0", "Ant1_0_1")
        unfold("union", "set_1") in("CF2_0", "Ant1_0_1")
        prop

        unfold("PRIME") in "Ant1_0_1"
        decompose
        forget("Ant1_0_1_1")
        unfold("ν") in "CF2_1"
        exL("CF2_1")
        paramod("CF2_1", hoa"0 + n * y = n * y", hof" x = n * y")
        forget("CF2_1_cut_0")
        cut("CF3", fof" x = 1")

        trivial

        eqL("CF3", "CF2_1")
        forget("CF3", "CF2_0", "CF")
        axiomTh

        forget("Suc_0", "Ant1")
        unfold("set_1") in "Suc_1"
        decompose
        trivial
      }
    }

    val Pi_1 = Lemma(
      ("Prime-Div" -> hof" 'PRIME-DIV'") +: ("x!=1" -> hof" ¬x = 1") +: (s"F[$k]" -> hof" ∀l (PRIME(l) <-> X(l))") +: Sequent() :+ ("Suc" -> hof"∃y (X(y) ∧ ν 0 y x)")
    ) {
      unfold("PRIME-DIV") in "Prime-Div"
      allL("Prime-Div", fov"x").forget
      impL

      trivial

      exL("Prime-Div")
      exR("Suc", fov"l").forget
      allL(s"F[$k]", fov"l").forget
      decompose
      impL(s"F[$k]_0")

      trivial

      forget("Prime-Div_0")
      andR

      trivial

      forget(s"F[$k]_0")
      unfold("DIV") in "Prime-Div_1"
      unfold("ν") in "Suc"
      exL
      exR(fov"m").forget
      forget(s"F[$k]_1", "x!=1")
      paramod("Suc", hoa" 0 + m * l = m * l", hoa"x = m*l")
      paramod("Suc", hoa" m * l = l * m", hoa" x = l * m")
      paramod("Suc", hoa" l * m = x", hoa" x = x")
      trivial
    }

    val psi1Right: LKProof = {
      val endSequent = (s"F[$k]" -> F(k).asInstanceOf[HOLFormula]) +: ("Prime-Div" -> hof" 'PRIME-DIV'") +: Sequent() :+ ("Suc" -> hof" compN(set_1(1))(x) -> ${S(k)}(x)")

      Lemma(endSequent) {
        decompose
        unfold("compN", "set_1") in "Suc_0"
        cut("CF", hof"∃y (${P(k)}(y) ∧ ν 0 y x)")

        unfold(s"F[$k]") in s"F[$k]"
        insert(Pi_1)

        forget("Prime-Div", s"F[$k]", "Suc_0")
        //insert(varrho1(k))
      }
    }
    // Proof of EXT, F[k], PRIME-DIV :- S[k] = comp({1})
    def psi1: LKProof = Lemma(
      ("EXT" -> extensionality) +: (s"F[$k]" -> F(k).asInstanceOf[HOLFormula]) +: ("Prime-Div" -> hof" 'PRIME-DIV'") +: Sequent() :+ "goal" -> hof" ${S(k)} = compN(set_1 1)"
    ) {
      chain("EXT")
      forget("EXT")
      allR("goal")
      andR("goal")

      insert(psi1Left)

      /*forget("Prime-Div")
      impR("goal")
      unfold("goal_1", "compN")
      cut(hof"¬ x = 1", "CF")

      forget("goal_1")
      cut(hof" ∃(y: i) (in(y, ${P(2)}: i>o) ∧ in(x, ν(0,y)))", "CF2")

      forget(s"F[$k]", "CF")*/

      /*forget("goal_0", s"F[$k]")
      unfold("goal_1", "set_1", "in")
      trivial*/
    }

    def proof(k: Int): LKProof = {
      require(k >= 0)
      ???
    }

    def F(k: Int) = Const(s"F[$k]", To)
    def S(k: Int) = Const(s"S[$k]", Ti -> To)
    def P(k: Int) = Const(s"P[$k]", Ti -> To)
  }
}

object PrimeProof {
  def main( args: Array[String] ): Unit = {
    val k = args( 0 ).toInt
    prime( k ).varrho2( 2 )
    ()
  }

  val oldProof = XMLProofDatabaseParser( "examples/prime/ceres_xml/prime1-2.xml.gz" ).proofs( 0 )._2
}
