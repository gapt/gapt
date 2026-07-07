fof(a1, axiom, ![X]: p(X, a, b), file('Problems/skolemizationContextVariablesOrder.p', a1)).
fof(c, conjecture, ?[Z]: ?[Y]: ![X]: p(X, Y, Z), file('Problems/skolemizationContextVariablesOrder.p', c)).
fof(nc, negated_conjecture, ![Z]: ![Y]: ?[X]: ~p(X, Y, Z), inference(negated_conjecture, [status(cth)], [c])).
fof(ncs1, plain, ![Z]: ![Y]: ~p(sK0(Y, Z), Y, Z), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0(Y, Z))], [nc])).
fof(i1, plain, ~p(sK0(a, b), a, b), inference(instance, [status(thm)], [ncs1])).
fof(i2, plain, p(sK0(a,b), a, b), inference(instance, [status(thm)], [a1])).
fof(refute, plain, $false, inference(contradiction, [status(thm)], [i1, i2])).
