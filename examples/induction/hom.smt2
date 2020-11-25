(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(declare-fun f (nat) nat)
(assert (forall ((x nat)) (= (f (s x)) (s (f x)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( o x)
    ( (s y1) (s (plus x y1))))))
(assert (forall ((x nat))
  (= (plus o x) x)))
(assert (forall ((x nat) (y nat))
  (= (plus (s x) y) (s (plus x y)))))

(prove (forall ((x nat)) (exists ((y nat))
  (= (plus y x) (f x)))))
