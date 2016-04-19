(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-fun P (nat) Bool)
(assert (P o))
(assert (forall ((x nat)) (=> (P x) (P (s x)))))

(assert-not (forall ((x nat)) (P x)))
(check-sat)
