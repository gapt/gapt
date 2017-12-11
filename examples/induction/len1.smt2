; Example from [Eri08] that requires introduction of addition.

(declare-datatypes () ((nat (o) (s (p nat)))))
(declare-sort i 0)
(declare-datatypes () ((list (nil) (cons (head i) (tail list)))))

(define-fun-rec len ((xs list)) nat
  (match xs
    (case (cons h t) (s (len t)))
    (case nil o)))

(define-fun-rec len1 ((xs list) (a nat)) nat
  (match xs
    (case (cons h t) (len1 t (s a)))
    (case nil a)))

(prove (forall ((x list))
  (= (len x) (len1 x o))))
