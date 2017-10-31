(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec even ((x nat)) Bool
  (match x
    (case (s x)
      (match x
        (case (s x) (even x))
        (case o false)))
    (case o true)))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus x y)))
    (case o x)))

(prove (forall ((x nat)) (even (plus x x))))
