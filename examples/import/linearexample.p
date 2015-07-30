% --------------------------------------------------------
%
% Problem:
% P(0), \forall x. P(x) -> P(f(x)) |- P(f^9(0))
%
% --------------------------------------------------------

fof(base_case, axiom, p(z)).

fof(induction_step, axiom, ![X]: ((p(X) => p(f(X))))).

%fof(goal, conjecture, p(f(f(f(f(f(f(f(f(f(z))))))))))).
fof(goal, conjecture, p(f(f(f(f(z)))))).
