; solve with: viper --treegrammar --cansolsize 3 3

(declare-datatypes ((nat 0)) (( (o) (s (p nat)))))
(define-fun-rec plus ((x nat) (y nat)) nat
  (match y
    (( o x)
    ( (s y1) (s (plus x y1))))))
(prove (forall ((x nat))
  (= (plus x (s o)) (plus (s o) x))))
