; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
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
(define-fun
  (par (a)
    (butlastConcat
       ((x (list a)) (y (list a))) (list a)
       (match y
         (case nil (butlast x))
         (case (cons z x2) (append x (butlast y)))))))
(assert-not
  (par (a)
    (forall ((xs (list a)) (ys (list a)))
      (= (butlast (append xs ys)) (butlastConcat xs ys)))))
(check-sat)
