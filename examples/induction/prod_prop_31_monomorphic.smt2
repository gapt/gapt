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
