; viper instprover escargot

(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-fun P (nat nat) Bool)
(assert (P o o))
(assert (forall ((x nat) (y nat)) (=> (P x y) (P (s x) y))))
(assert (forall ((x nat) (y nat)) (=> (P x y) (P x (s y)))))

(assert-not (forall ((x nat)) (P x x)))
(check-sat)
