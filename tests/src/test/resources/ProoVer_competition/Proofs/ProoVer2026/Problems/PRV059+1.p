%------------------------------------------------------------------------------
% File     : PRV059+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, ! [X] : (? [Y] : (relA(X,Y)))).

fof(b1, axiom, ! [X] : ((midA1(X) => midA2(X)))).

fof(b2, axiom, ! [X] : ((midA2(X) => midA3(X)))).

fof(c, conjecture, ? [X] : (? [Y] : (relA(X,Y)))).
% SZS output end ListOfFormulae
