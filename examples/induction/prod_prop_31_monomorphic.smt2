; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996

; for performance:
; solve with: viper --treegrammar2 --cansolsize 2 3 --gramw scomp

(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(define-fun-rec
  qrev
    ((x list) (y list)) list
    (match x
      (case nil y)
      (case (cons z xs) (qrev xs (cons z y)))))
(prove (forall ((x list)) (= (qrev (qrev x nil) nil) x)))
