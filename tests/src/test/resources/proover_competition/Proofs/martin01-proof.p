% should fail: negated_conjecture only works on conjectures
fof(f7, plain, $false, inference(resolution, [], [f6,f5])).
fof(f6, plain, q(X0,s1(X0)), inference(cnf, [], [f3])).
fof(f5, negated_conjecture, ~q(s2,X1), inference(negated_conjecture, [], [f4])).
fof(f4, plain,
    ? [X1] : (q(s2,X1) | p(s2)),
    inference(skolemize, [status(esa), new_symbols(skolem, [s2]), skolemize(X1, s2)], [f2])).
fof(f3, plain,
    ! [X0] : (q(X0,s1(X0)) & p(X0)),
    inference(skolemize, [status(esa), new_symbols(skolem, [s1]), skolemize(X1, s1(X0))], [f1])).
fof(f2,conjecture,(
  ! [X0] : ? [X1] : (q(X0,X1) | p(X0))),
  file('Problems/martin01.p',unknown)).
fof(f1,axiom,(
  ! [X0] : ? [X1] : (q(X0,X1) & p(X0))),
  file('Problems/martin01.p',unknown)).
