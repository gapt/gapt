(declare-sort i 0)
(declare-datatypes () ((list (nil) (cons (head i) (tail list)))))

(define-fun-rec append ((xs list) (ys list)) list
  (match xs
    (case (cons x xs) (cons x (append xs ys)))
    (case nil ys)))

(declare-const a list)
(declare-const b list)
(prove (forall ((x list))
  (= (append (append x a) b)
     (append x (append a b)))))
