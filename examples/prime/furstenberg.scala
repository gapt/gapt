package gapt.examples.prime

import gapt.expr._
import gapt.formats.babel.{Notation, Precedence}
import gapt.proofs.gaptic._
import gapt.proofs.lk.LKProof

/**
 * Furstenberg's topological proof of the infinitude of primes.
 *
 * furstenberg(k) proves that there are more than k primes.
 */
case class furstenberg(k: Int) extends PrimeDefinitions {

  ctx += Notation.Infix("=_s", Precedence.infixRel)
  ctx += hof"(A =_s B) = (∀(x:nat) (A x ↔ B x))"

  /* -------------
   * | Subproofs |
   * -------------
   */

  val deMorgan1 = Lemma(hols":- compN(union (X:nat>o) Y) =_s intersection(compN X)(compN Y)") {
    unfold("=_s").in("g")
    allR
    unfold("compN", "intersection", "union") in "g"
    prop
  }

  val intersectionOpen: LKProof = Lemma(hols"O(X), O(Y) :- O(intersection X Y)") {
    unfold("O").in("h_0", "h_1", "g")
    allR
    impR
    allL("h_0", hov"m:nat").forget
    unfold("intersection") in "g_0"
    andL
    impL left trivial

    exL(hov"l_0:nat")
    allL("h_1", hov"m:nat").forget
    impL left trivial

    forget("g_0_0", "g_0_1")
    exL(hov"l_1:nat")
    exR(le" (l_0 + 1) * l_1 + l_0").forget
    cut("CF", hoa" (l_0 + 1) * l_1 + l_0 + 1 = (l_0 + 1) * (l_1 + 1)") left theory

    eql("CF", "g_1")
    forget("CF")
    unfold("subset", "intersection") in "g_1"
    decompose
    andR

    by {
      forget("h_1")
      unfold("subset") in "h_0"
      allL("h_0", hov"n:nat").forget
      impL right trivial

      forget("g_1_1")
      unfold("ν").in("g_1_0", "h_0")
      exL
      exR(le"n_0 * (l_1 + 1)").forget
      theory
    }

    by {
      forget("h_0")
      unfold("subset") in "h_1"
      allL("h_1", hov"n:nat").forget
      impL right trivial

      forget("g_1_1")
      unfold("ν").in("g_1_0", "h_1")
      exL
      exR(le"n_0 * (l_0 + 1)").forget
      theory
    }
  }

  val unionClosed = Lemma(hols"C(X : nat>o), C(Y) :- C(union X Y)") {
    unfold("C").in("h_0", "h_1", "g")
    cut("CF", hof" compN(union (X : nat>o) Y) =_s intersection(compN X)(compN Y)") left insert(deMorgan1)

    cut("g_2", hof"O(intersection (compN X) (compN Y))") left by { insert(intersectionOpen) }

    // TODO: prove congruence lemmas
    unfold("=_s").in("CF")
    unfold("O", "subset").in("g", "g_2")
    simp.w("CF").on("g")
  }

  val progClosed = Lemma(hols"PRE, REM, '0<l': 0 < l :- C(ν 0 l)") {
    cut("CF", hof" U(0,l) =_s compN(ν 0 l)") left by {
      forget("PRE", "g")
      unfold("=_s").in("CF")
      allR
      andR

      by {
        forget("REM")
        unfold("compN", "U") in "CF"
        decompose
        unfold("ν").in("CF_0_1", "CF_1")
        exL("CF_0_1")
        exL("CF_1")
        eql("CF_0_1", "CF_1")
        forget("CF_0_1")
        cut("tri", hof"¬0 = i") left by {
          forget("CF_0_0_0", "CF_1", "0<l")
          decompose
          quasiprop
        }

        forget("CF_0_0_1")
        decompose
        theory
      }

      by {
        impR
        unfold("REM") in "REM"
        allL(hov"l:nat").forget
        impL left trivial

        forget("0<l")
        allL(hov"x:nat").forget
        decompose
        unfold("U") in "CF_1"
        exR(hov"k:nat").forget
        andR right trivial

        andR left trivial

        unfold("compN") in "CF_0"
        decompose
        eql("CF_1", "REM_1")
        trivial
      }
    }

    unfold("C") in "g"
    forget("REM")

    // TODO: congruence lemmas
    cut("g_2", hof"O(U 0 l)") right by {
      unfold("O", "subset").in("g", "g_2")
      unfold("=_s").in("CF")
      simp.w("CF").on("g_2")
    }
    forget("g"); renameLabel("g_2").to("g")

    forget("CF")
    unfold("O") in "g"
    decompose
    unfold("PRE") in "PRE"
    allL("PRE", hov"l:nat").forget
    impL left trivial

    forget("0<l")
    exL
    exR(hov"m_0:nat").forget
    rewrite rtl "PRE" in "g_1"
    forget("PRE")
    unfold("subset") in "g_1"
    unfold("U") in "g_0"
    decompose
    unfold("U") in "g_1_1"
    exR(hov"i:nat").forget
    andR

    by { andR; trivial; prop }

    by {
      forget("g_0_0_0", "g_0_0_1")
      unfold("ν").in("g_0_1", "g_1_0", "g_1_1")
      decompose
      exR(le"n_0 + n_1").forget
      rewrite.many.ltr("g_0_1", "g_1_0")
      theory
    }
  }

  val compCompProof = Lemma(hols":- comp: compN(compN(X)) =_s X") {
    unfold("=_s").in("comp")
    allR("comp", hov"x:nat")
    unfold("compN") in "comp"
    prop
  }

  // Proof that if complement(X) is closed, X is open
  val openClosedProof = Lemma(hols"C: C(compN(X)) :- O: O(X)") {
    unfold("C") in "C"
    cut("CF", hof" compN(compN(X: nat>o)) =_s X") left by {
      // Left subproof of the cut:
      forget("C", "O")
      insert(compCompProof)
    }

    // Right subproof of the cut:
    // TODO: congruence lemmas
    unfold("=_s").in("CF")
    unfold("O", "subset").in("C", "O")
    simp.w("CF").on("C")
  }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma(hols":- nonempty: ¬empty(set_1(1))") {
    unfold("empty", "set_1") in "nonempty"
    decompose
    exR("nonempty", le"1")
    trivial
  }

  // Proof that {1} is finite
  val singletonFinite = Lemma(hols"infinite: INF (set_1 1) :-") {
    unfold("INF", "set_1") in "infinite"
    allL("infinite", le"1").forget
    exL("infinite")
    theory
  }

  // Proof of INF(Set), Set subset X :- INF(X).
  // Set and X are free.
  val infiniteSubset = Lemma(hols"subset_inf: INF(Set), subset: subset Set X :- set_inf: INF(X)") {
    unfold("INF").in("subset_inf", "set_inf")
    allR("set_inf")
    allL("subset_inf", hov"k:nat").forget
    exL("subset_inf")
    exR("set_inf", hov"l:nat").forget
    unfold("subset") in "subset"
    chain("subset")
    trivial
  }

  // Proof that every nonempty open set is infinite.
  val phi2 = Lemma(hols"open: O(X), nonempty: ¬ empty X :- infinite: INF X") {
    unfold("empty") in "nonempty"
    unfold("O") in "open"
    decompose
    allL(hov"n:nat").forget
    impL left trivial

    forget("nonempty")
    exL
    cut("CF", hof"INF(ν(n, l+1))") right insert(infiniteSubset)

    // Left subproof: ν(n, l+1) is infinite
    forget("open", "infinite")
    unfold("INF") in "CF"
    allR
    unfold("ν").in("CF")
    exR(le"n + (k+1)*l", le"k+1").forget
    // TODO(gabriel): the following instances change the witness
    // exR( le"n * (l + (1 + 1)) + l * (k+1)", le"n + (k + 1)" ).forget
    theory
  }

  /**
   * Proof of x ∈ S[n] :- ∃y ( y ∈ P[n] ∧ x ∈ ν(0,y) )
   */
  def varrho2(n: Int): LKProof = {
    val endSequent = hols"S $n x :- ∃y (P $n y ∧ ν 0 y x)"

    n match {
      case 0 =>
        Proof(endSequent) {
          unfold("S") in "h_0"
          exR(le"p 0").forget
          andR

          by {
            unfold("P", "set_1") in "g"
            trivial
          }

          by {
            unfold("ν").in("h_0", "g")
            exL
            exR(hov"n:nat").forget
            trivial
          }
        }

      case _ =>
        Proof(endSequent) {
          unfold("S", "union").atMost(2) in "h_0"
          orL
          by {
            cut("CF", hof"∃y (P ${n - 1} y ∧ ν 0 y x)") left insert(varrho2(n - 1))

            forget("h_0")
            exL
            exR(hov"y:nat").forget
            andR
            by {
              unfold("P").atMost(1) in "g"
              unfold("union", "set_1") in "g"
              prop
            }
            by {
              andL
              unfold("ν").in("CF_1", "g")
              exL
              exR("g", hov"n:nat").forget
              trivial
            }
          }
          by {
            exR(le"p $n").forget
            andR
            by {
              forget("h_0")
              unfold("P", "union", "set_1") in "g"
              orR
              trivial
            }
            by {
              unfold("ν").in("h_0", "g")
              exL
              exR("g", hov"n:nat").forget
              trivial
            }
          }
        }

    }
  }

  // Proof of F[k] :- x ∈ S[k] -> x ∈ comp({1})
  val psi1Left: LKProof =
    Lemma(hols"h: F $k :- S $k x -> compN(set_1(1))(x)") {
      decompose
      unfold("compN") in "g_1"
      cut("CF", hof"¬x = 1") left by {
        forget("g_1")
        cut("CF2", hof" ∃y (P $k y ∧ ν(0,y)(x))") left insert(varrho2(k))

        forget("g_0")
        unfold("F") in "h"
        decompose
        allL("h", hov"y:nat")
        decompose
        forget("h_0_0", "h")
        impL left by {
          unfold("P").in("CF2_0", "h_0_1")
          unfold("union", "set_1").in("CF2_0", "h_0_1")
          prop
        }

        unfold("PRIME") in "h_0_1"
        decompose
        forget("h_0_1_1")
        unfold("ν") in "CF2_1"
        decompose
        theory
      }

      unfold("set_1") in "g_1"
      decompose
      trivial
    }

  val Pi_1 = Lemma(hols"'Prime-Div': 'PRIME-DIV', 'x!=1': ¬x = 1, Fk: ∀l (PRIME(l) <-> X(l)) :- ∃y (X(y) ∧ ν 0 y x)") {
    unfold("PRIME-DIV") in "Prime-Div"
    allL("Prime-Div", hov"x:nat").forget
    impL left trivial

    exL("Prime-Div")
    exR("g", hov"l:nat").forget
    allL("Fk", hov"l:nat").forget
    decompose
    impL("Fk_0") left trivial

    forget("Prime-Div_0")
    andR left trivial

    unfold("DIV") in "Prime-Div_1"
    unfold("ν") in "g"
    exL
    exR(hov"m:nat").forget
    theory
  }

  def lambda(n: Int): LKProof = {
    val endSequent = hols"P $n y, ν 0 y x :- S $n x"

    n match {
      case 0 =>
        Proof(endSequent) {
          unfold("P", "set_1") in "h_0"
          unfold("S") in "g"
          eql("h_0", "g")
          trivial
        }

      case _ =>
        Proof(endSequent) {
          unfold("P", "union").atMost(2) in "h_0"
          unfold("S", "union").atMost(2) in "g"
          orR
          orL left insert(lambda(n - 1))

          unfold("set_1") in "h_0"
          eql("h_0", "g_1")
          trivial
        }
    }
  }

  val psi1Right: LKProof =
    Lemma(hols"Fk: F $k, 'Prime-Div': 'PRIME-DIV' :- compN(set_1(1))(x) -> S $k x") {
      decompose
      unfold("compN", "set_1") in "g_0"
      cut("CF", hof"∃y (P $k y ∧ ν 0 y x)") left by { unfold("F").in("Fk"); insert(Pi_1) }

      forget("Prime-Div", "Fk", "g_0")
      decompose
      insert(lambda(k))
    }
  // Proof of F[k], PRIME-DIV :- S[k] = comp({1})
  val psi1: LKProof = Lemma(hols"Fk: F $k, 'Prime-Div': 'PRIME-DIV' :- S $k =_s compN(set_1 1)") {
    unfold("=_s").in("g")
    allR("g")
    andR("g")
    by { insert(psi1Left) }
    by { insert(psi1Right) }
  }

  val FR: LKProof = Lemma(hols"Fk: F $k :- Rk: R $k") {
    unfold("R") in "Rk"
    allR
    unfold("F") in "Fk"
    allL(hov"y:nat")
    andL
    trivial
  }

  def RQ(n: Int): LKProof = {
    val endSequent = hols"Rn: R $n :- Qn: Q $n"

    n match {
      case 0 =>
        Proof(endSequent) {
          unfold("Q") in "Qn"
          unfold("R") in "Rn"
          allL(le"p 0").forget
          impL right trivial

          unfold("P", "set_1") in "Rn"
          trivial
        }

      case _ =>
        Proof(endSequent) {
          unfold("Q").atMost(1) in "Qn"
          cut("Rn1", hof"R ${n - 1}") left by {
            unfold("R") in "Rn1"
            allR
            impR
            unfold("R") in "Rn"
            allL(hov"y:nat").forget
            impL right trivial

            unfold("P").atMost(1) in "Rn"
            unfold("union") in "Rn"
            prop
          }

          andR left insert(RQ(n - 1))

          forget("Rn1")
          unfold("R") in "Rn"
          allL(le"p $n").forget
          impL right trivial

          unfold("P").atMost(1) in "Rn"
          unfold("union", "set_1") in "Rn"
          orR
          trivial
        }
    }
  }

  val FQ: LKProof = Lemma(hols"F $k :- Q $k") {
    cut(s"Rk", hof"R $k") left insert(FR)
    insert(RQ(k))
  }

  val pgt0: LKProof = Lemma(hols"prime: PRIME(n) :- pos: 0 < n") {
    cut("CF", hof" 1 < n") left by {
      forget("pos")
      unfold("PRIME") in "prime"
      andL
      trivial
    }

    forget("prime")
    cut("CF2", hof" 0 + 1 = 1") left theory

    eql("CF2", "CF")
    theory
  }

  def psi2Right(n: Int): LKProof = {
    val endSequent = hols"PRE, Qn: Q $n, REM :- C: C (S $n)"

    n match {
      case 0 =>
        Proof(endSequent) {
          unfold("Q") in "Qn"
          cut("zero_lt_p0", hof" 0 < p 0") left insert(pgt0)

          unfold("S") in "C"
          insert(progClosed)
        }

      case _ =>
        Proof(endSequent) {
          unfold("Q") atMost 1 in "Qn"
          andL
          cut(s"zero_lt_pn", hof" 0 < p $n") left insert(pgt0)

          unfold("S") atMost 1 in "C"
          cut("CF", hof" C(ν 0 (p $n))") left insert(progClosed)

          cut("CF2", hof" C(S ${n - 1})") left insert(psi2Right(n - 1))

          insert(unionClosed)
        }
    }
  }

  val psi2: LKProof = Lemma(hols"F $k, REM, PRE :- C (S $k)") {
    cut("Q", hof"Q $k") left insert(FQ)
    insert(psi2Right(k))
  }

  val proof: LKProof =
    Lemma(hols"F $k, REM, PRE, 'PRIME-DIV' :-") {
      cut("INF {1}", hof" INF (set_1 1)") right insert(singletonFinite)
      cut("nonempty {1}", hof" ¬ empty (set_1 1)") left insert(singletonNonempty)

      cut("O {1}", hof" O (set_1 1)") right insert(phi2)
      cut("C compN{1}", hof" C (compN(set_1 1))") right insert(openClosedProof)
      cut("CF", hof" S $k =_s compN(set_1 1)") left insert(psi1)

      // TODO: congruence lemmas
      cut("C", hof"C (S $k)") right by {
        unfold("=_s", "compN").in("CF")
        unfold("C", "O", "subset", "compN").in("C", "C compN{1}")
        simp.w("CF").on("C")
        simp.on("C compN{1}")
      }
      forget("C compN{1}"); renameLabel("C").to("C compN{1}")

      insert(psi2)
    }
}
object furstenberg3 extends furstenberg(3)
