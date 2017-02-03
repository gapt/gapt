; Property from "Productive Use of Failure in Inductive Proof",
; Andrew Ireland and Alan Bundy, JAR 1996
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(define-fun-rec
  plus
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z) (S (plus z y)))))
(define-fun one () Nat (S Z))
(define-fun-rec
  mult
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z) (plus y (mult z y)))))
(define-fun-rec
  qfac
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z) (qfac z (mult x y)))))
(define-fun-rec
  fac
    ((x Nat)) Nat
    (match x
      (case Z (S Z))
      (case (S y) (mult x (fac y)))))
(assert-not (forall ((x Nat)) (= (fac x) (qfac x one))))
(check-sat)
