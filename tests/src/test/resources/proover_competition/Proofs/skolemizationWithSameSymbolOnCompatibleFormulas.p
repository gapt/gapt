fof(a1, axiom, ![X]: p(X), file('Problems/skolemizationWithSameSymbolOnCompatibleFormulas.p', a1)).
fof(c, conjecture, ![X]: p(X), file('Problems/skolemizationWithSameSymbolOnCompatibleFormulas.p', c)).
fof(nc, negated_conjecture, ?[X]: ~p(X), inference(negated_conjecture, [status(cth)], [c])).
fof(ncs1, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
fof(ncs2, plain, ~p(sK0), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(X, sK0)], [nc])).
fof(i, plain, p(sK0), inference(instance, [status(thm)], [a1])).
fof(refute, plain, $false, inference(contradiction, [status(thm)], [i, ncs1, ncs2])).
