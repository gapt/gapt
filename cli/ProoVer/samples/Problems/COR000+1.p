%------------------------------------------------------------------------------
% File     : COR000+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, p(a) & ~p(b)).
fof(c, conjecture, ?[X] : ~(p(X) => ![Y] : (p(Y)))).
% SZS output end ListOfFormulae
