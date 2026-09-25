%------------------------------------------------------------------------------
% File     : PRV063+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a0, axiom, p1_topo(a)).

fof(a1, axiom, ! [X] : ((p1_topo(X) => p2_topo(X)))).

fof(a2, axiom, ! [X] : ((p2_topo(X) => p3_topo(X)))).

fof(a3, axiom, ! [X] : ((p3_topo(X) => p4_topo(X)))).

fof(a4, axiom, ! [X] : ((p4_topo(X) => p5_topo(X)))).

fof(a5, axiom, ! [X] : ((p5_topo(X) => p6_topo(X)))).

fof(c, conjecture, p6_topo(a)).
% SZS output end ListOfFormulae
