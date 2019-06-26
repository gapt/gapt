; Example from [Eri08] that requires introduction of concatenation.

(declare-sort int 0)
(declare-const I int)

(declare-datatypes ((list 0)) (( (nil) (cons (head int) (tail list)))))

(define-fun-rec ones ((xs list)) list
  (match xs
    (( (cons h t) (cons I (ones t)))
    ( nil nil))))

(define-fun-rec ones1 ((xs list) (a list)) list
  (match xs
    (( (cons h t) (ones1 t (cons I a)))
    ( nil a))))

(prove (forall ((x list))
  (= (ones x) (ones1 x nil))))
