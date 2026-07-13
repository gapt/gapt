% eprover proof with problems:
% - negated_conjecture must always have a conjecture as parent
fof(c1, conjecture, p(a), file('Problems/martin05.p', c1)).
fof(a1, axiom, ![X1] : (p(X1)), file('Problems/martin05.p', a1)).
fof(c_0_2, negated_conjecture, ~p(a), inference(negated_conjecture,[status(cth)],[c1])).
fof(c_0_3, plain, ~p(a), inference(fof_nnf,[status(thm)],[c_0_2])).
cnf(c_0_4, plain, (~p(a)), inference(split_conjunct,[status(thm)],[c_0_3])).
cnf(c_0_5, axiom, ![X1] : (p(X1)), file('Problems/martin05.p', a1)).
cnf(c_0_6, plain, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_4, c_0_5])]), ['proof']).
