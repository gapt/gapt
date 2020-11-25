(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec even ((x nat)) Bool
  (match x
    (( (s x) (not (even x)))
    ( o true))))
(define-fun-rec odd ((x nat)) Bool
  (match x
    (( (s x) (not (odd x)))
    ( o false))))

(prove (forall ((x nat))
  (= (even x) (odd (s x)))))
