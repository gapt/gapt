(declare-sort i 0)
(declare-datatypes () ((list (nil) (cons (head i) (tail list)))))

(define-fun-rec append ((xs list) (ys list)) list
  (match xs
    (case (cons x xs) (cons x (append xs ys)))
    (case nil ys)))

(define-fun-rec elem ((x i) (xs list)) Bool
  (match xs
    (case (cons x2 xs) (or (= x x2) (elem x xs)))
    (case nil false)))

(assert-not (forall ((x i) (y list) (z list))
  (=> (elem x z) (elem x (append y z)))))
(check-sat)
