(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec pred ((x nat)) nat
  (match x (( (s x) x) ( o o))))

(define-fun-rec minus ((x nat) (y nat)) nat
  (match y
    (( (s y) (pred (minus x y)))
    ( o x))))

(prove (forall ((x nat)) (= (minus o x) o)))
