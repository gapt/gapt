% eprover proof with problems:
% - c_0_2: negated_conjecture must always have a conjecture as parent and negated_conjecture as inference name
%          unclear: can thm and cth inferences be chained?
% - c_0_3 / c_0_4 / c_0_6: negated_conjecture must be plain inference here

fof(c1, conjecture, p(a), file('Problems/martin05.p', c1)).
cnf(a1, axiom, (p(X1)), file('Problems/martin05.p', a1)).
fof(c_0_2, negated_conjecture, ~p(a), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[c1])])).
fof(c_0_3, negated_conjecture, ~p(a), inference(fof_nnf,[status(thm)],[c_0_2])).
cnf(c_0_4, negated_conjecture, (~p(a)), inference(split_conjunct,[status(thm)],[c_0_3])).
cnf(c_0_5, axiom, (p(X1)), file('Problems/martin05.p', a1)).
cnf(c_0_6, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_4, c_0_5])]), ['proof']).
