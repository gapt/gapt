(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec plus1 ((x nat) (y nat)) nat
  (match x
    (( (s x) (s (plus1 x y)))
    ( o y))))
(define-fun-rec plus2 ((x nat) (y nat)) nat
  (match y
    (( (s y) (s (plus1 x y)))
    ( o x))))

(prove (forall ((x nat))
  (= (plus1 x x) (plus2 x x))))
