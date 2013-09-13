============================== Prover9 ===============================
Prover9 (64) version 2009-11A, November 2009.
Process 4653 was started by shaolin on chercheur-125.msr-inria.inria.fr,
Fri Sep 13 11:57:17 2013
The command was "prover9".
============================== end of head ===========================

============================== INPUT =================================

formulas(assumptions).
p(a) | p(b).
(all x (q(x,f(x)) | q(x,g(x)))).
end_of_list.

formulas(goals).
(exists x (p(x) & (exists y q(x,y)))).
end_of_list.

============================== end of input ==========================

============================== PROCESS NON-CLAUSAL FORMULAS ==========

% Formulas that are not ordinary clauses:
1 (all x (q(x,f(x)) | q(x,g(x)))) # label(non_clause).  [assumption].
2 (exists x (p(x) & (exists y q(x,y)))) # label(non_clause) # label(goal).  [goal].

============================== end of process non-clausal formulas ===

============================== PROCESS INITIAL CLAUSES ===============

% Clauses before input processing:

formulas(usable).
end_of_list.

formulas(sos).
p(a) | p(b).  [assumption].
q(x,f(x)) | q(x,g(x)).  [clausify(1)].
-p(x) | -q(x,y).  [deny(2)].
end_of_list.

formulas(demodulators).
end_of_list.

============================== PREDICATE ELIMINATION =================

No predicates eliminated.

============================== end predicate elimination =============

Auto_denials:  (non-Horn, no changes).

Term ordering decisions:
Predicate symbol precedence:  predicate_order([ p, q ]).
Function symbol precedence:  function_order([ a, b, f, g ]).
After inverse_order:  (no changes).
Unfolding symbols: (none).

Auto_inference settings:
  % set(binary_resolution).  % (non-Horn)
  % set(neg_ur_resolution).  % (non-Horn, less than 100 clauses)

Auto_process settings:
  % set(factor).  % (non-Horn)
  % set(unit_deletion).  % (non-Horn)

kept:      3 p(a) | p(b).  [assumption].
kept:      4 q(x,f(x)) | q(x,g(x)).  [clausify(1)].
kept:      5 -p(x) | -q(x,y).  [deny(2)].

============================== end of process initial clauses ========

============================== CLAUSES FOR SEARCH ====================

% Clauses after input processing:

formulas(usable).
end_of_list.

formulas(sos).
3 p(a) | p(b).  [assumption].
4 q(x,f(x)) | q(x,g(x)).  [clausify(1)].
5 -p(x) | -q(x,y).  [deny(2)].
end_of_list.

formulas(demodulators).
end_of_list.

============================== end of clauses for search =============

============================== SEARCH ================================

% Starting search at 0.01 seconds.

given #1 (I,wt=4): 3 p(a) | p(b).  [assumption].

given #2 (I,wt=8): 4 q(x,f(x)) | q(x,g(x)).  [clausify(1)].

given #3 (I,wt=5): 5 -p(x) | -q(x,y).  [deny(2)].

given #4 (A,wt=6): 6 -p(x) | q(x,f(x)).  [resolve(5,b,4,b)].

given #5 (T,wt=6): 7 q(b,f(b)) | p(a).  [resolve(6,a,3,b)].

given #6 (T,wt=4): 8 p(a) | -p(b).  [resolve(7,a,5,b)].

given #7 (T,wt=2): 9 p(a).  [resolve(8,b,3,b),merge(b)].

============================== PROOF =================================

% Proof 1 at 0.01 (+ 0.00) seconds.
% Length of proof is 12.
% Level of proof is 7.
% Maximum clause weight is 8.000.
% Given clauses 7.

1 (all x (q(x,f(x)) | q(x,g(x)))) # label(non_clause).  [assumption].
2 (exists x (p(x) & (exists y q(x,y)))) # label(non_clause) # label(goal).  [goal].
3 p(a) | p(b).  [assumption].
4 q(x,f(x)) | q(x,g(x)).  [clausify(1)].
5 -p(x) | -q(x,y).  [deny(2)].
6 -p(x) | q(x,f(x)).  [resolve(5,b,4,b)].
7 q(b,f(b)) | p(a).  [resolve(6,a,3,b)].
8 p(a) | -p(b).  [resolve(7,a,5,b)].
9 p(a).  [resolve(8,b,3,b),merge(b)].
10 q(a,f(a)).  [resolve(9,a,6,a)].
11 -q(a,x).  [ur(5,a,9,a)].
12 $F.  [resolve(11,a,10,a)].

============================== end of proof ==========================

============================== STATISTICS ============================

Given=7. Generated=9. Kept=9. proofs=1.
Usable=4. Sos=0. Demods=0. Limbo=1, Disabled=6. Hints=0.
Kept_by_rule=0, Deleted_by_rule=0.
Forward_subsumed=0. Back_subsumed=3.
Sos_limit_deleted=0. Sos_displaced=0. Sos_removed=0.
New_demodulators=0 (0 lex), Back_demodulated=0. Back_unit_deleted=0.
Demod_attempts=0. Demod_rewrites=0.
Res_instance_prunes=0. Para_instance_prunes=0. Basic_paramod_prunes=0.
Nonunit_fsub_feature_tests=0. Nonunit_bsub_feature_tests=9.
Megabytes=0.04.
User_CPU=0.01, System_CPU=0.00, Wall_clock=0.

============================== end of statistics =====================

============================== end of search =========================

THEOREM PROVED

Exiting with 1 proof.

Process 4653 exit (max_proofs) Fri Sep 13 11:57:17 2013
