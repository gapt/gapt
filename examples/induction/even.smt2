(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec even ((x nat)) Bool
  (match x
    (( (s x)
      (match x
        (( (s x) (even x))
        ( o false))))
    ( o true))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( (s y) (s (plus x y)))
    ( o x))))

(prove (forall ((x nat)) (even (plus x x))))
