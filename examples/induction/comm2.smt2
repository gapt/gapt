(declare-datatypes () ((nat (o) (s (p nat)))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case o x)
    (case (s y1) (s (plus x y1)))))
;- (assert (forall ((x nat))
;-   (= (plus o x) x)))
;- (assert (forall ((x nat) (y nat))
;-   (= (plus (s x) y) (s (plus x y)))))
(assert-not (forall ((x nat) (y nat))
  (= (plus x y) (plus y x))))
(check-sat)
