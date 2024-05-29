package gapt.examples.tip.grammars

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.tactics.ForwardChain

object simp_expr_unambig1 extends TacticsProof {

  // Inductive types
  ctx += InductiveType(ty"Tok", hoc"'C' :Tok", hoc"'D' :Tok", hoc"'X' :Tok", hoc"'Y' :Tok", hoc"'Pl' :Tok")
  ctx += InductiveType(ty"list", hoc"'nil' :list", hoc"'cons' :Tok>list>list")
  ctx += InductiveType(ty"E", hoc"'Plus' :E>E>E", hoc"'EX' :E", hoc"'EY' :E")

  // Function constants
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'lin' :E>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:Tok, x1:list): list): Tok) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:Tok, x1:list): list): list) = x1,
        def_Plus_0: ∀x0 ∀x1 (Plus_0(Plus(x0:E, x1:E): E): E) = x0,
        def_Plus_1: ∀x0 ∀x1 (Plus_1(Plus(x0:E, x1:E): E): E) = x1,
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:Tok, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_lin_0: ∀a   ∀b   (lin(Plus(a:E, b:E): E): list) =
             append(append(append(append(cons(C:Tok, nil:list): list, lin(a)): list,
                        cons(Pl, nil)), lin(b)), cons(D, nil)),
        def_lin_1: (lin(EX:E): list) = cons(#c(X: Tok), nil:list),
        def_lin_2: (lin(EY:E): list) = cons(#c(Y: Tok), nil:list),
        constr_inj_0: ¬(C:Tok) = D,
        constr_inj_1: ¬(C:Tok) = #c(X: Tok),
        constr_inj_2: ¬(C:Tok) = #c(Y: Tok),
        constr_inj_3: ¬(C:Tok) = Pl,
        constr_inj_4: ¬(D:Tok) = #c(X: Tok),
        constr_inj_5: ¬(D:Tok) = #c(Y: Tok),
        constr_inj_6: ¬(D:Tok) = Pl,
        constr_inj_7: ¬#c(X: Tok) = #c(Y: Tok),
        constr_inj_8: ¬#c(X: Tok) = Pl,
        constr_inj_9: ¬#c(Y: Tok) = Pl,
        constr_inj_10: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Tok, y1:list),
        constr_inj_11: ∀x0 ∀x1 ¬(Plus(x0:E, x1:E): E) = EX,
        constr_inj_12: ∀x0 ∀x1 ¬(Plus(x0:E, x1:E): E) = EY,
        constr_inj_13: ¬(EX:E) = EY
        :-
        goal: ∀u ∀v ((lin(u:E): list) = lin(v) → u = v)
  """

  val theory = Sequent(sequent.antecedent, Nil)

  //  val sequent = theory ++ Sequent(
  //    Nil,
  //    bench.toSequent.succedent.map { case f => "goal" -> f } )

  val cong_pos =
    (
      ("h1" -> hof"!x0 !x1 tail(cons(x0, x1)) = x1") +:
        ("ass" -> hof"cons(z,x) = cons(z,y)") +:
        Sequent() :+
        ("conc" -> hof"(x:list) = y")
    )
  val cong_pos_proof = Lemma(cong_pos) {
    allL("h1", hov"z:Tok", hov"x:list")
    allL("h1", hov"z:Tok", hov"y:list")
    quasiprop
  }

  val cong_neg =
    (
      ("h0" -> hof"!x0 !x1 head(cons(x0, x1)) = x0") +:
        ("ass" -> hof"- ( ( u:Tok ) = v )") +:
        ("conc" -> hof"cons(u,x) = cons(v,y)") +:
        Sequent()
    )
  val cong_neg_proof = Lemma(cong_neg) {
    allL("h0", hov"u:Tok", hov"x:list")
    allL("h0", hov"v:Tok", hov"y:list")
    quasiprop
  }

  // the symmetric variant cong_neg_symm of cong_neg is necessary for the insert-tactic to work properly (FIXME?)
  val cong_neg_symm =
    (
      ("h0" -> hof"!x0 !x1 head(cons(x0, x1)) = x0") +:
        ("ass" -> hof"- ( ( v:Tok ) = u )") +:
        ("conc" -> hof"cons(u,x) = cons(v,y)") +:
        Sequent()
    )
  val cong_neg_symm_proof = Lemma(cong_neg_symm) {
    allL("h0", hov"u:Tok", hov"x:list")
    allL("h0", hov"v:Tok", hov"y:list")
    quasiprop
  }

  val app_assoc = hof"!x !y !z append( x, append( y, z )) = append( append( x, y ), z )"

  val lem = hof"!a !b !x !y ( append( lin(a), x ) = append( lin(b), y ) ->  ( a = b  & x = y ))"

  val lem_proof = Lemma(("app_assoc" -> app_assoc) +: theory :+ ("goal" -> lem)) {
    allR
    induction(hov"a:E") // outer case distinction

    // -- a starts with Plus
    allR
    induction(hov"b:E") // inner case distion

    // - a starts with Plus, b starts with Plus
    allR; allR; impR
    rewrite.many ltr "def_lin_0" in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many.ltr("def_append_0", "def_append_1") in "goal_0"

    allL("IHa_0", le"b_0:E").forget
    allL("IHa_1", le"b_1:E").forget
    forget("IHb_0", "IHb_1")

    cut(
      "step_1",
      hof"""append(lin(a_0), cons(Pl, append(lin(a_1), cons(D, x)))) =
            append(lin(b_0), cons(Pl, append(lin(b_1), cons(D, y))))"""
    ); insert(cong_pos_proof)
    forget("goal_0")
    allL("IHa_0", le"cons(Pl, append(lin(a_1), cons(D, x)))", le"cons(Pl, append(lin(b_1), cons(D, y)))").forget
    impL("IHa_0"); trivial
    andL("IHa_0")
    forget("step_1")

    cut("step_2", hof"append(lin(a_1), cons(D, x)) = append(lin(b_1), cons(D, y))"); insert(cong_pos_proof)
    forget("IHa_0_1")
    allL("IHa_1", le"cons(D, x)", le"cons(D, y)").forget
    impL("IHa_1"); trivial
    andL("IHa_1")
    forget("step_2")

    cut("step_3", hof"(x:list) = y"); insert(cong_pos_proof)
    quasiprop

    // - a starts with Plus, b is EX
    allR; allR; impR
    rewrite.many.ltr("def_lin_0", "def_lin_1") in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many.ltr("def_append_0", "def_append_1") in "goal_0"
    insert(cong_neg_proof)

    // - a starts with Plus, b is EY
    allR; allR; impR
    rewrite.many.ltr("def_lin_0", "def_lin_2") in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many.ltr("def_append_0", "def_append_1") in "goal_0"
    insert(cong_neg_proof)

    // -- a is EX
    allR
    induction(hov"b:E") // inner case distion

    // - a is EX, b starts with Plus
    allR; allR; impR
    rewrite.many.ltr("def_lin_0", "def_lin_1") in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many.ltr("def_append_0", "def_append_1") in "goal_0"
    insert(cong_neg_symm_proof)

    // - a is EX, b is EX
    allR; allR; impR
    rewrite.many.ltr("def_append_0", "def_append_1", "def_lin_1") in "goal_0"
    cut("step_1", hof"(x:list) = y"); insert(cong_pos_proof)
    quasiprop

    // - a is EX, b is EY
    allR; allR; impR
    rewrite.many.ltr("def_append_0", "def_append_1", "def_lin_1", "def_lin_2") in "goal_0"
    insert(cong_neg_proof)

    // -- a is EY
    allR
    induction(hov"b:E") // inner case distion

    // - a is EY, b starts with Plus
    allR; allR; impR
    rewrite.many.ltr("def_lin_0", "def_lin_2") in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many.ltr("def_append_0", "def_append_1") in "goal_0"
    insert(cong_neg_symm_proof)

    // - a is EY, b is EX
    allR; allR; impR
    rewrite.many.ltr("def_append_0", "def_append_1", "def_lin_1", "def_lin_2") in "goal_0"
    insert(cong_neg_symm_proof)

    // - a is EY, b is EY
    allR; allR; impR
    rewrite.many.ltr("def_append_0", "def_append_1", "def_lin_2") in "goal_0"
    cut("step_1", hof"(x:list) = y"); insert(cong_pos_proof)
    quasiprop
  }

  val proof = Lemma(("app_assoc" -> app_assoc) +: sequent) {
    allR; allR

    induction(hov"u:E") // outer case distinction

    // -- u starts with Plus
    induction(hov"v:E") // inner case distion

    // - u starts with Plus, v starts with Plus
    cut("lem", lem); insert(lem_proof) // introduce lemma

    impR
    rewrite.many.ltr("def_lin_0", "def_append_1", "def_append_0") in "goal_0"
    cut(
      "eq1",
      hof"""append(append(append(lin(u_0), cons(Pl, nil)), lin(u_1)), cons(D, nil)) =
            append(append(append(lin(v_0), cons(Pl, nil)), lin(v_1)), cons(D, nil))"""
    ); insert(cong_pos_proof)
    forget("goal_0")

    rewrite.many rtl "app_assoc" in "eq1"
    forwardChain("lem", OnLabel("eq1"))

    forget("eq1")

    andL("lem_0")
    rewrite.many.ltr("def_append_1", "def_append_0") in "lem_0_1"
    cut("eq2", hof"append(lin(u_1), cons(D, nil)) = append(lin(v_1), cons(D, nil))"); insert(cong_pos_proof)

    forwardChain("lem", OnLabel("eq2"))
    quasiprop

    // - u starts with Plus, v is EX
    impR
    rewrite.many.ltr("def_lin_1", "def_lin_0") in "goal_0"
    rewrite.many rtl ("app_assoc") in "goal_0"
    rewrite ltr "def_append_1" in "goal_0"
    insert(cong_neg_proof)

    // - u starts with Plus, v is EY
    impR
    rewrite.many.ltr("def_lin_2", "def_lin_0") in "goal_0"
    rewrite.many rtl ("app_assoc") in "goal_0"
    rewrite ltr "def_append_1" in "goal_0"
    insert(cong_neg_proof)

    // -- u is EX
    induction(hov"v:E") // inner case distion

    // - u is EX, v starts with Plus
    impR
    rewrite.many.ltr("def_lin_1", "def_lin_0") in "goal_0"
    rewrite.many rtl ("app_assoc") in "goal_0"
    rewrite ltr "def_append_1" in "goal_0"
    insert(cong_neg_symm_proof)

    // - u is EX, v is EX
    quasiprop

    // - u is EX, v is EY
    impR
    rewrite.many.ltr("def_lin_1", "def_lin_2") in "goal_0"
    insert(cong_neg_proof)

    // -- u is EY
    induction(hov"v:E") // inner case distion

    // - u is EY, v starts with Plus
    impR
    rewrite.many.ltr("def_lin_2", "def_lin_0") in "goal_0"
    rewrite.many rtl ("app_assoc") in "goal_0"
    rewrite ltr "def_append_1" in "goal_0"
    insert(cong_neg_symm_proof)

    // - u is EY, v is EX
    impR
    rewrite.many.ltr("def_lin_1", "def_lin_2") in "goal_0"
    insert(cong_neg_symm_proof)

    // - u is EY, v is EY
    quasiprop
  }
}
