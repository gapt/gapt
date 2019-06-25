; solve with: viper --treegrammar --cansolsize 2 2 --qtys ""
(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))

(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( (s y) (s (plus x y)))
    ( o x))))

(prove (forall ((x nat))
  (= (plus x (s x)) (plus (s x) x))))
