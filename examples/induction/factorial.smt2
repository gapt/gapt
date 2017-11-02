(declare-datatypes () ((nat (o) (s (p nat)))))

(declare-fun times (nat nat) nat)
(assert (forall ((x nat) (y nat) (z nat))
  (= (times (times x y) z) (times x (times y z)))))
(assert (forall ((x nat))
  (= (times (s o) x) (times x (s o)) x)))

(define-fun-rec f ((x nat)) nat
  (match x
    (case o (s o))
    (case (s y) (times x (f y)))))

(define-fun-rec g ((x nat) (y nat)) nat
  (match y
    (case o x)
    (case (s y1) (g (times x y) y1))))

(prove (forall ((x nat))
  (= (g (s o) x) (f x))))
