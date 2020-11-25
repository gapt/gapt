; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996

; for performance:
; solve with: viper --treegrammar --cansolsize 2 3 --gramw scomp

(declare-datatype
  list (par (a) ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  qrev
  (par (a) (((x (list a)) (y (list a))) (list a)))
  (match x
    ((nil y)
     ((cons z xs) (qrev xs (cons z y))))))
(prove
  (par (a)
    (forall ((x (list a))) (= (qrev (qrev x (_ nil a)) (_ nil a)) x))))
