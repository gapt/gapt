(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec even ((x nat)) Bool
  (match x
    (case (s x) (not (even x)))
    (case o true)))
(define-fun-rec odd ((x nat)) Bool
  (match x
    (case (s x) (not (odd x)))
    (case o false)))

(prove (forall ((x nat))
  (= (even x) (odd (s x)))))
