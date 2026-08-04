%------------------------------------------------------------------------------
% File     : PRV064+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, ! [X] : ((man(X) => mortal(X)))).

fof(a2, axiom, ! [X] : ((mortal(X) => dies(X)))).

fof(a3, axiom, ! [X] : ((dies(X) => finite_life(X)))).

fof(a4, axiom, ! [X] : ((finite_life(X) => ~(eternal(X))))).

fof(a5, axiom, man(socrates)).

fof(c, conjecture, ~(eternal(socrates))).
% SZS output end ListOfFormulae
