(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-fun P (nat nat) Bool)
(assert (P o o))
(assert (forall ((x nat) (y nat)) (=> (P x y) (P (s x) y))))
(assert (forall ((x nat) (y nat)) (=> (P x y) (P x (s y)))))

(prove (forall ((x nat)) (P x x)))
