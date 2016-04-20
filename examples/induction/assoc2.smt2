(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus x y)))
    (case o x)))

(assert-not (forall ((x nat))
  (= (plus (plus (s (s o)) x) x)
     (plus (s (s o)) (plus x x)))))
(check-sat)
