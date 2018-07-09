(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec even1 ((x nat)) Bool
  (match x
    (case (s x) (not (even1 x)))
    (case o true)))
(define-fun-rec even2 ((x nat)) Bool
  (match x
    (case (s x)
      (match x
        (case (s x) (even2 x))
        (case o false)))
    (case o true)))

(prove (forall ((x nat))
  (= (even1 x) (even2 x))))
