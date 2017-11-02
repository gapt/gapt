; Property from "Case-Analysis for Rippling and Inductive Proof",
; Moa Johansson, Lucas Dixon and Alan Bundy, ITP 2010
(declare-datatypes ()
  ((Nat :source Definitions.Nat (Z :source Definitions.Z)
     (S :source Definitions.S (proj1-S Nat)))))
(define-fun-rec
  |-2| :source Definitions.-
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z Z)
      (case (S z)
        (match y
          (case Z x)
          (case (S x2) (|-2| z x2))))))
(define-fun-rec
  +2 :source Definitions.+
    ((x Nat) (y Nat)) Nat
    (match x
      (case Z y)
      (case (S z) (S (+2 z y)))))
(prove
  :source Properties.prop_06
  (forall ((n Nat) (m Nat)) (= (|-2| n (+2 n m)) Z)))
