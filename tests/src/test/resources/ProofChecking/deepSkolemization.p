fof(a1, axiom, ![X]: ?[Y]: ![Z]: p(X, Y, Z), file('Problems/deepSkolemization.p', a1)).
fof(c, conjecture, ![X]: ?[Y]: ![Z]: p(X, Y, Z), file('Problems/deepSkolemization.p', c)).
fof(nc, negated_conjecture, ?[X]: ![Y]: ?[Z]: p(X,Y,Z), inference(negated_conjecture, [status(cth)], [c])).
fof(ncs1, plain, ?[X]: ![Y]: p(X,Y,sK0(Y)), inference(skolemize, [status(esa), new_symbols(skolem, [sK0]), skolemize(Z, sK0(Y))], [nc])).
fof(i, plain, p(sK0), inference(instance, [status(thm)], [ncs1])).
fof(refute, plain, $false, inference(contradiction, [status(thm)], [i, ncs1])).
