%------------------------------------------------------------------------------
% File     : PRV057+1.p : ProoVer 2026
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a0, axiom, p1_cs(a)).

fof(a1, axiom, ! [X] : ((p1_cs(X) => p2_cs(X)))).

fof(a2, axiom, ! [X] : ((p2_cs(X) => p3_cs(X)))).

fof(a3, axiom, ! [X] : ((p3_cs(X) => p4_cs(X)))).

fof(a4, axiom, ! [X] : ((p4_cs(X) => p5_cs(X)))).

fof(a5, axiom, ! [X] : ((p5_cs(X) => p6_cs(X)))).

fof(c, conjecture, p6_cs(a)).
% SZS output end ListOfFormulae
