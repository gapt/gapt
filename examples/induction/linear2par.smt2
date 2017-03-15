; viper --treegrammar --qtys ""

(declare-datatypes () ((nat (o) (s (p nat)))))

(define-fun-rec P ((x nat) (y nat) (z nat)) Bool
  (match z
    (case o true)
    (case (s z) (P x y z))))

(assert-not (forall ((x nat) (y nat)) (P x y y)))
(check-sat)
