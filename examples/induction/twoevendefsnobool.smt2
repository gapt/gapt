(declare-datatypes () ((mybool (t) (f))))
(define-fun-rec mynot ((x mybool)) mybool
  (match x (case t f) (case f t)))

(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec even1 ((x nat)) mybool
  (match x
    (case (s x) (mynot (even1 x)))
    (case o t)))
(define-fun-rec even2 ((x nat)) mybool
  (match x
    (case (s x)
      (match x
        (case (s x) (even2 x))
        (case o f)))
    (case o t)))

(prove (forall ((x nat))
  (= (even1 x) (even2 x))))
