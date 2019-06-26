; Example from [Eri08] that requires introduction of addition.

(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))
(declare-sort i 0)
(declare-datatypes ((list 0)) (( (nil) (cons (head i) (tail list)))))

(define-fun-rec len ((xs list)) nat
  (match xs
    (( (cons h t) (s (len t)))
    ( nil o))))

(define-fun-rec len1 ((xs list) (a nat)) nat
  (match xs
    (( (cons h t) (len1 t (s a)))
    ( nil a))))

(prove (forall ((x list))
  (= (len x) (len1 x o))))
