%------------------------------------------------------------------------------
% File     : correct_proof : ProoVer 2026
% Proof    : Problems/correct_problem.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1, axiom, p(a) & ~p(b), file('Problems/correct_problem.p',a1)).
fof(c, conjecture, ?[X] : ~(p(X) => ![Y] : (p(Y))), file('Problems/correct_problem.p',c)).
fof(s1, negated_conjecture, ![X] : (p(X) => ![Y] : (p(Y))), inference(negated_conjecture, [status(cth)], [c])).
fof(f1, plain, $false, inference(consequence, [status(thm)], [s1, a1])).
% SZS output end Proof
