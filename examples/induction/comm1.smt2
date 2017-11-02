; solve with: viper --treegrammar --cansolsize 3 3 --qtys ""
; FIXME: interestingly, this problem always with fails with smaller canonical solutions

(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus x y)))
    (case o x)))

(prove (forall ((x nat))
  (= (plus x (s o)) (plus (s o) x))))
