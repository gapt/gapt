(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec even1 ((x nat)) Bool
  (match x
    (( (s x) (not (even1 x)))
    ( o true))))
(define-fun-rec even2 ((x nat)) Bool
  (match x
    (( (s x)
      (match x
        (( (s x) (even2 x))
        ( o false))))
    ( o true))))

(prove (forall ((x nat))
  (= (even1 x) (even2 x))))
