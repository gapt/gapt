veriT 201410 - the SMT-solver veriT (UFRN/LORIA).
success
success
success
success
success
success
success
success
unsat
success
(set .c1 (input :conclusion ((p a))))
(set .c2 (input :conclusion ((and (= (f a b) (f (f a b) b)) (= (p (f (f a b) b)) (p a))))))
(set .c3 (input :conclusion ((not (p (f a b))))))
(set .c4 (and :clauses (.c2) :conclusion ((= (f a b) (f (f a b) b)))))
(set .c5 (and :clauses (.c2) :conclusion ((= (p (f (f a b) b)) (p a)))))
(set .c6 (equiv1 :clauses (.c5) :conclusion ((not (p (f (f a b) b))) (p a))))
(set .c7 (equiv2 :clauses (.c5) :conclusion ((p (f (f a b) b)) (not (p a)))))
(set .c8 (resolution :clauses (.c7 .c1) :conclusion ((p (f (f a b) b)))))
(set .c9 (eq_congruent_pred :conclusion ((not (= (f a b) (f (f a b) b))) (not (p (f (f a b) b))) (p (f a b)))))
(set .c10 (resolution :clauses (.c9 .c4 .c8 .c3) :conclusion ()))
