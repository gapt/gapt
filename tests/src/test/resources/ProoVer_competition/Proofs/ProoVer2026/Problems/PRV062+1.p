%------------------------------------------------------------------------------
% File     : PRV062+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, p_ef(a)).

fof(a2, axiom, ~(p_ef(a))).

fof(a3, axiom, q_ef(a)).

fof(b1, axiom, ! [X] : ((q_ef(X) => r_ef(X)))).

fof(c, conjecture, r_ef(a)).
% SZS output end ListOfFormulae
