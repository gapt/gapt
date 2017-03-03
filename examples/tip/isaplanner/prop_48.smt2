; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun
  (par (a)
    (null
       ((x (list a))) Bool
       (match x
         (case nil true)
         (case (cons y z) false)))))
(define-fun-rec
  last
    ((x (list Nat))) Nat
    (match x
      (case nil Z)
      (case (cons y z)
        (match z
          (case nil y)
          (case (cons x2 x3) (last z))))))
(define-fun-rec
  (par (a)
    (butlast
       ((x (list a))) (list a)
       (match x
         (case nil (as nil (list a)))
         (case (cons y z)
           (match z
             (case nil (as nil (list a)))
             (case (cons x2 x3) (cons y (butlast z)))))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (cons z (append xs y)))))))
(assert-not
  (forall ((xs (list Nat)))
    (=> (not (null xs))
      (= (append (butlast xs) (cons (last xs) (as nil (list Nat))))
        xs))))
(check-sat)
