(declare-datatypes ((mybool 0)) (( (t) (f))))
(define-fun-rec mynot ((x mybool)) mybool
  (match x (( t f) ( f t))))

(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec even1 ((x nat)) mybool
  (match x
    (( (s x) (mynot (even1 x)))
    ( o t))))
(define-fun-rec even2 ((x nat)) mybool
  (match x
    (( (s x)
      (match x
        (( (s x) (even2 x))
        ( o f))))
    ( o t))))

(prove (forall ((x nat))
  (= (even1 x) (even2 x))))
