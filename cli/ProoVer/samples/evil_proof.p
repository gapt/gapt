%------------------------------------------------------------------------------
% File     : evil_proof : ProoVer 2026
% Proof    : Problems/evil_problem.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1, axiom, p(a), file('Problems/evil_problem.p',a1)).
fof(c, conjecture, ![X] : (p(X)), file('Problems/evil_problem.p',c)).
fof(s1, negated_conjecture, ![X] : (~p(X)), inference(negated_conjecture, [status(cth)], [c])).
fof(f1, plain, $false, inference(consequence, [status(thm)], [s1, a1])).
% SZS output end Proof
