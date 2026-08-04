%------------------------------------------------------------------------------
% File     : PRV034+1.p : ProoVer 2026
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, p(a)).
fof(a2, axiom, ![X]: (p(X) => q(X))).
fof(a3, axiom, ![X]: (p(X) => r(X))).
fof(c, conjecture, q(a) & r(a)).
% SZS output end ListOfFormulae
