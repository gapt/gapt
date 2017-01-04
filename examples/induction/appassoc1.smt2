(declare-sort i 0)
(declare-datatypes () ((list (nil) (cons (head i) (tail list)))))

(define-fun-rec append ((xs list) (ys list)) list
  (match xs
    (case (cons x xs) (cons x (append xs ys)))
    (case nil ys)))

(assert-not (forall ((x list))
  (= (append (append x x) x)
     (append x (append x x)))))
(check-sat)
