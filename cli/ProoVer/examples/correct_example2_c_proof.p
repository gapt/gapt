%------------------------------------------------------------------------------
% File     : example2_proof : ProoVer 2026
% Proof    : Problems/example2_c.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1, axiom, ![X]: (p(X) => p(f(X))), file('Problems/example2_c.p',ax1)).
fof(a2, axiom, p(a), file('Problems/example2_c.p',ax2)).
fof(c, conjecture, p(f(f(a))), file('Problems/example2_c.p',c)).
fof(s1, negated_conjecture, ~p(f(f(a))), inference(negated_conjecture, [status(cth)], [c])).
fof(s2, plain, p(a) => p(f(a)), inference(instantiate, [status(thm)], [a1])).
fof(s3, plain, p(f(a)) => p(f(f(a))), inference(instantiate, [status(thm)], [a1])).
fof(s4, plain, p(f(f(a))), inference(horn, [status(thm)], [a2, s1, s2, s3])).
fof(s5, plain, $false, inference(consequence, [status(thm)], [s1, s4])).
% SZS output end Proof
