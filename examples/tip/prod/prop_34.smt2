; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z) (S (plus z y)))))
(define-fun-rec
  mult2
    ((x Nat) (y Nat) (z Nat)) Nat
    (match x
      (case Z z)
      (case (S x2) (mult2 x2 y (plus y z)))))
(define-fun-rec
  mult
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z) (plus y (mult z y)))))
(assert-not
  (forall ((x Nat) (y Nat)) (= (mult x y) (mult2 x y Z))))
(check-sat)
