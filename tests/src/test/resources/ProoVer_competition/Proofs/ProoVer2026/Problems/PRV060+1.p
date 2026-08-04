%------------------------------------------------------------------------------
% File     : PRV060+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, ! [X] : (? [Y] : (relB(X,Y)))).

fof(b1, axiom, ! [X] : ((midB1(X) => midB2(X)))).

fof(b2, axiom, ! [X] : ((midB2(X) => midB3(X)))).

fof(c, conjecture, ? [X] : (? [Y] : (relB(X,Y)))).
% SZS output end ListOfFormulae
