; solve with: viper --treegrammar --cansolsize 3 3
; FIXME: interestingly, this problem always with fails with smaller canonical solutions

(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( (s y) (s (plus x y)))
    ( o x))))

(prove (forall ((x nat))
  (= (plus x (s o)) (plus (s o) x))))
