; solve with: viper --treegrammar2 --cansolsize 2 2 --qtys ""
(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (case (s y) (s (plus x y)))
    (case o x)))

(prove (forall ((x nat))
  (= (plus x (s x)) (plus (s x) x))))
