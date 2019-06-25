(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( o x)
    ( (s y1) (s (plus x y1))))))
;- (assert (forall ((x nat))
;-   (= (plus o x) x)))
;- (assert (forall ((x nat) (y nat))
;-   (= (plus (s x) y) (s (plus x y)))))
(prove (forall ((x nat) (y nat))
  (= (plus x y) (plus y x))))
