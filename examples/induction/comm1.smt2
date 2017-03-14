; FIXME: interestingly, this problem always with fails with smaller canonical solutions
; viper --treegrammar --cansolsize 3 3 --qtys ""

(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus x y)))
    (case o x)))

(assert-not (forall ((x nat))
  (= (plus x (s o)) (plus (s o) x))))
(check-sat)
