%------------------------------------------------------------------------------
% File     : PRV002+1.p : ProoVer 2026
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(a1, axiom, ~(![X]: ?[Y]: ![Z]: ( p(X,Y,Z) | ?[X]: ![W]: ( q(X,Y,Z,W) & ?[Y]: r(X,Y,Z,W) ) ))).
fof(c, conjecture, ~(![X]: ?[Y]: ![Z]: ( p(X,Y,Z) | ?[X]: ![W]: ( q(X,Y,Z,W) & ?[Y]: r(X,Y,Z,W) ) ))).
% SZS output end ListOfFormulae
