(declare-sort i 0)
(declare-datatypes ((list 0)) (( (nil) (cons (head i) (tail list)))))

(define-fun-rec append ((xs list) (ys list)) list
  (match xs
    (( (cons x xs) (cons x (append xs ys)))
    ( nil ys))))

(define-fun-rec elem ((x i) (xs list)) Bool
  (match xs
    (( (cons x2 xs) (or (= x x2) (elem x xs)))
    ( nil false))))

(prove (forall ((x i) (y list) (z list))
  (=> (elem x z) (elem x (append y z)))))
