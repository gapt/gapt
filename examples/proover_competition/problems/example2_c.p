%------------------------------------------------------------------------------
% File     : example2_c : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(ax1, axiom, ![X]: (p(X) => p(f(X)))).
fof(ax2, axiom, p(a)).
fof(c, conjecture, p(f(f(a)))).
% SZS output end ListOfFormulae
