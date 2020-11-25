(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( (s y) (s (plus x y)))
    ( o x))))

(prove (forall ((x nat))
  (= (plus (plus (s (s o)) x) x)
     (plus (s (s o)) (plus x x)))))
