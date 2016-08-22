; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996

; for performance:
; viper cansolsize 2,2

(declare-sort sk 0)
(declare-datatypes () ((list (nil) (cons (head sk) (tail list)))))
(define-fun-rec
  qrev
    ((x list) (y list)) list
    (match x
      (case nil y)
      (case (cons z xs) (qrev xs (cons z y)))))
(assert-not (forall ((x list)) (= (qrev (qrev x nil) nil) x)))
(check-sat)
