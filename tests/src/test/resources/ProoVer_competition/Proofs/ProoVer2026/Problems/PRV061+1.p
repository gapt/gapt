%------------------------------------------------------------------------------
% File     : PRV061+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, p_dup(a)).

fof(b1, axiom, ! [X] : ((p_dup(X) => q_dup(X)))).

fof(b2, axiom, ! [X] : ((q_dup(X) => r_dup(X)))).

fof(c, conjecture, r_dup(a)).
% SZS output end ListOfFormulae
