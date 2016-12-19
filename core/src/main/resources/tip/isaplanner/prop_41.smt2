; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  (par (a)
    (take
       ((x Nat) (y (list a))) (list a)
       (match x
         (case Z (as nil (list a)))
         (case (S z)
           (match y
             (case nil (as nil (list a)))
             (case (cons x2 x3) (cons x2 (take z x3)))))))))
(define-fun-rec
  (par (a b)
    (map2
       ((x (=> a b)) (y (list a))) (list b)
       (match y
         (case nil (as nil (list b)))
         (case (cons z xs) (cons (@ x z) (map2 x xs)))))))
(assert-not
  (par (a b)
    (forall ((n Nat) (f (=> b a)) (xs (list b)))
      (= (take n (map2 f xs)) (map2 f (take n xs))))))
(check-sat)
