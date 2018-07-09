; solve with: viper --treegrammar --qtys witness --tchksize 0.5 1 --cansolsize 2 2
(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-sort witness 0)
(declare-fun f (witness) witness)
(declare-fun g (witness) witness)

(declare-fun P (nat witness) Bool)
(assert (forall ((y witness)) (P o y)))
(assert (forall ((x nat) (y witness))
  (=> (and (P x (f y)) (P x (g y))) (P (s x) y))))

(declare-const c witness)
(prove (forall ((x nat)) (P x c)))
