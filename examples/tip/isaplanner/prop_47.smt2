; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((Tree (Leaf)
     (Node (Node_0 (Tree a)) (Node_1 a) (Node_2 (Tree a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  (par (a)
    (mirror
       ((x (Tree a))) (Tree a)
       (match x
         (case Leaf (as Leaf (Tree a)))
         (case (Node l y r) (Node (mirror r) y (mirror l)))))))
(define-fun-rec
  max2
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z)
        (match y
          (case Z x)
          (case (S x2) (S (max2 z x2)))))))
(define-fun-rec
  (par (a)
    (height
       ((x (Tree a))) Nat
       (match x
         (case Leaf Z)
         (case (Node l y r) (S (max2 (height l) (height r))))))))
(assert-not
  (par (a)
    (forall ((b (Tree a))) (= (height (mirror b)) (height b)))))
(check-sat)
