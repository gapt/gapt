fof(a1, axiom, p, file('Problems/correctRefutationWithIncorrectAdditionalInference.p', a1)).
fof(c, conjecture, p, file('Problems/correctRefutationWithIncorrectAdditionalInference.p', c)).
fof(nc, negated_conjecture, ~p, inference(negated_conjecture, [status(cth)], [c])).
fof(refute, plain, $false, inference(contradiction, [status(thm)], [a1, nc])).
fof(incorrect, plain, q, inference(inf, [status(thm)], [a1])).
