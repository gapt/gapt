(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec plus1 ((x nat) (y nat)) nat
  (match x
    (case (s x) (s (plus1 x y)))
    (case o y)))
(define-fun-rec plus2 ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus1 x y)))
    (case o x)))

(prove (forall ((x nat))
  (= (plus1 x x) (plus2 x x))))
