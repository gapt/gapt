; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(define-fun-rec
  (par (a b)
    (zip
       ((x (list a)) (y (list b))) (list (Pair a b))
       (match x
         (case nil (as nil (list (Pair a b))))
         (case (cons z x2)
           (match y
             (case nil (as nil (list (Pair a b))))
             (case (cons x3 x4) (cons (Pair2 z x3) (zip x2 x4)))))))))
(define-fun
  (par (a b)
    (zipConcat
       ((x a) (y (list a)) (z (list b))) (list (Pair a b))
       (match z
         (case nil (as nil (list (Pair a b))))
         (case (cons y2 ys) (cons (Pair2 x y2) (zip y ys)))))))
(assert-not
  (par (a b)
    (forall ((x a) (xs (list a)) (ys (list b)))
      (= (zip (cons x xs) ys) (zipConcat x xs ys)))))
(check-sat)
