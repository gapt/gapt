(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-fun P (nat nat) Bool)
(assert (forall ((x nat)) (P x o)))
(assert (forall ((x nat) (y nat)) (=> (P (s x) y) (P x (s y)))))

(assert-not (forall ((x nat)) (P o x)))
(check-sat)
