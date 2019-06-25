; solve with: viper --treegrammar --cansolsize 2 3

(declare-sort i 0)
(declare-datatypes ((list 0)) (( (nil) (cons (head i) (tail list)))))

(define-fun-rec append ((xs list) (ys list)) list
  (match xs
    (( (cons x xs) (cons x (append xs ys)))
    ( nil ys))))

(prove (forall ((x list))
  (= (append x nil) x)))
