namespace gapt

open tactic expr

namespace lk

lemma LogicalAxiom {a} (main1 : a) (main2 : ¬a) : false := main2 main1
lemma BottomAxiom (main : false) : false := main
lemma TopAxiom (main : ¬true) : false := main ⟨⟩
lemma ReflexivityAxiom {α : Type} {a : α} (main : a ≠ a) : false := main (eq.refl a)
lemma NegLeftRule {a} (main : ¬a) (aux : ¬¬a) : false := aux main
lemma NegRightRule {a} (main : ¬¬a) (aux : ¬a) : false := main aux
lemma AndLeftRule {a b} (main : a ∧ b) (aux : a → b → false) : false :=
aux main^.left main^.right
lemma AndRightRule {a b} (main : ¬(a ∧ b)) (aux1 : ¬¬a) (aux2 : ¬¬b) : false :=
aux1 $ λa, aux2 $ λb, main ⟨a,b⟩
lemma OrLeftRule {a b} (main : a ∨ b) (aux1 : ¬a) (aux2 : ¬b) : false :=
begin cases main, contradiction, contradiction end
lemma OrRightRule {a b} (main : ¬(a ∨ b)) (aux : ¬a → ¬b → false) : false :=
aux (main ∘ or.inl) (main ∘ or.inr)
lemma ImpLeftRule {a b} (main : a → b) (aux1 : ¬¬a) (aux2 : ¬b) : false := aux1 (aux2 ∘ main)
lemma ImpRightRule {a b : Prop} (main : ¬(a → b)) (aux : a → ¬b → false) : false :=
main (classical.by_contradiction ∘ aux)
lemma ForallLeftRule {α} {P : α → Prop} (t) (main : ∀x, P x) (aux : ¬P t) : false := aux (main t)
lemma ForallRightRule {α} {P : α → Prop} (main : ¬∀x, P x) (aux : Πx, ¬P x → false) : false :=
begin apply main, intro x, apply classical.by_contradiction, intro, apply aux, assumption end
lemma ExistsLeftRule {α} {P : α → Prop} (main : ∃x, P x) (aux : Πx, P x → false) : false :=
begin cases main, apply aux, assumption end
lemma ExistsRightRule {α} {P : α → Prop} (t) (main : ¬∃x, P x) (aux : ¬¬P t) : false :=
begin apply aux, intro hp, apply main, existsi t, assumption end
lemma EqualityLeftRule1 {α} (c : α → Prop) (t s) (main1 : t=s) (main2 : c s) (aux : ¬c t) : false :=
begin apply aux, rw main1, assumption end
lemma EqualityRightRule1 {α} (c : α → Prop) (t s) (main1 : t=s) (main2 : ¬c s) (aux : ¬¬c t) : false :=
begin apply aux, rw main1, assumption end
lemma EqualityLeftRule2 {α} (c : α → Prop) (t s) (main1 : s=t) (main2 : c s) (aux : ¬c t) : false :=
EqualityLeftRule1 c t s main1^.symm main2 aux
lemma EqualityRightRule2 {α} (c : α → Prop) (t s) (main1 : s=t) (main2 : ¬c s) (aux : ¬¬c t) : false :=
EqualityRightRule1 c t s main1^.symm main2 aux
lemma CutRule (a : Prop) (aux1 : ¬¬a) (aux2 : ¬a) : false := aux1 aux2

lemma unpack_target_disj.cons {a b} (next : ¬a → b) : a ∨ b :=
classical.by_cases or.inl (or.inr ∘ next)
lemma unpack_target_disj.singleton {a} : ¬¬a → a := classical.by_contradiction
private meta def unpack_target_disj : list name → command
| [] := skip
| [h] := do tgt ← target,
            apply $ app (const ``gapt.lk.unpack_target_disj.singleton []) tgt,
            intro h, skip
| (h::hs) := do tgt ← target,
                a ← return $ tgt^.app_fn^.app_arg,
                b ← return $ tgt^.app_arg,
                apply $ app_of_list (const ``gapt.lk.unpack_target_disj.cons []) [a, b],
                intro h,
                unpack_target_disj hs

meta def sequent_formula_to_hyps (ant suc : list name) : command := do
intro_lst ant, unpack_target_disj suc

-- private meta def mk_ctr_aux (ctr_name : name) : tactic expr := do
-- ctr ← mk_const ,
-- return (default _)

meta def mk_InductionRule (type_name : name) : command := do
type ← return $ const type_name [],
env ← get_env, ctrs ← return $ env^.constructors_of type_name,
P ← mk_local_def `P (imp type prop),
t ← mk_local_def `t type,
main ← mk_local_def `main (app (const ``not []) (app P t)),
skip

end lk

end gapt

section
open gapt.lk
example {t : Type} {P : t → Prop} : (∀x, P x) → (∀x, P x ∧ P x) :=
begin
sequent_formula_to_hyps [`h1] [`h2],
apply (ForallRightRule h2), intros x h3,
apply (ForallLeftRule x h1), intros h4,
apply (AndRightRule h3),
intro h5, apply (LogicalAxiom h4 h5),
intro h5, apply (LogicalAxiom h4 h5)
end
end

-- constant i : Type
-- inductive list_0 : Type
-- | nil_0 : list_0
-- | cons_0 : (i -> (list_0 -> list_0))
-- open list_0
-- lemma gapt.lk.InductionRule (P : list_0 → Prop) (t : list_0) (main : ¬P t)
-- (aux1 : ¬P nil_0 → false) (aux2 : Πx xs, P xs → ¬P (cons_0 x xs) → false) : false :=
-- begin apply main, clear main, induction t,
-- apply classical.by_contradiction, apply aux1,
-- apply classical.by_contradiction, apply aux2, assumption end
