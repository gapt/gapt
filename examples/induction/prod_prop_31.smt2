; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996

; for performance:
; solve with: viper --treegrammar2 --cansolsize 2 3 --gramw scomp

(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  (par (a)
    (qrev
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (qrev xs (cons z y)))))))
(prove
  (par (a)
    (forall ((x (list a)))
      (= (qrev (qrev x (_ nil a)) (_ nil a)) x))))
