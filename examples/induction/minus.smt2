(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec pred ((x nat)) nat
  (match x (case (s x) x) (case o o)))

(define-fun-rec minus ((x nat) (y nat)) nat
  (match y
    (case (s y) (pred (minus x y)))
    (case o x)))

(assert-not (forall ((x nat)) (= (minus o x) o)))
(check-sat)
