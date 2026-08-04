%------------------------------------------------------------------------------
% File     : PRV017+1.p : ProoVer 2026
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, ![X]: (greek(X) => human(X))).
fof(a2, axiom, ![X]: (human(X) => (mortal(X) | immortal(X)))).
fof(a3, axiom, ![X]: (immortal(X) => god(X))).
fof(a4, axiom, greek(socrates)).
fof(a5, axiom, ~god(socrates)).
fof(c, conjecture, mortal(socrates)).
% SZS output end ListOfFormulae
