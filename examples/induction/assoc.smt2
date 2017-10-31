(declare-datatypes () ((nat (o) (s (p nat)))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case o x)
    (case (s y1) (s (plus x y1)))))
(prove (forall ((x nat))
  (= (plus (plus x x) x) (plus x (plus x x)))))
