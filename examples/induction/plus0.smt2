(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( o x)
    ( (s y1) (s (plus x y1))))))
(prove (forall ((x nat))
  (= (plus o x) x)))
