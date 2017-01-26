; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  (par (a)
    (append
       ((x (list a)) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons z xs) (cons z (append xs y)))))))
(define-fun-rec
  (par (a)
    (rev
       ((x (list a))) (list a)
       (match x
         (case nil (as nil (list a)))
         (case (cons y xs) (append (rev xs) (cons y (as nil (list a)))))))))
(define-fun-rec
  (par (a)
    (qrevflat
       ((x (list (list a))) (y (list a))) (list a)
       (match x
         (case nil y)
         (case (cons xs xss) (qrevflat xss (append (rev xs) y)))))))
(define-fun-rec
  (par (a)
    (revflat
       ((x (list (list a)))) (list a)
       (match x
         (case nil (as nil (list a)))
         (case (cons xs xss) (append (revflat xss) (rev xs)))))))
(assert-not
  (par (a)
    (forall ((x (list (list a))))
      (= (revflat x) (qrevflat x (as nil (list a)))))))
(check-sat)
