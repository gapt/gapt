% ------------------------------------------------------ 
% There exists two irrational numbers x and y such that
% x to the power of y is rational.
%
% (TPTP format problem file)
% ------------------------------------------------------ 

fof(a, axiom, i(sr2)).
fof(b, axiom, ~i(two)).
fof(c, axiom, times(sr2,sr2) = two).
fof(d, axiom, ![X,Y,Z] : exp(exp(X, Y), Z) = exp(X, times(Y,Z))).
fof(e, axiom, ![X] : exp(X, two) = times(X,X)).
fof(f, conjecture, ?[X,Y] : (~i(exp(X,Y)) & i(X) & i(Y))).

