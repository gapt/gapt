%------------------------------------------------------------------------------
% File     : PRV011+1.p : ProoVer 2026
%------------------------------------------------------------------------------
% SZS output start ListOfFormulae
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
      ( q(f(c))
     => a = a ) ).

fof(s1,axiom,
    ! [X5] :
      ( ! [X6] : t
    <=> ( r(c,X5)
       => q(X5) ) ) ).

fof(s2,axiom,
    ! [X7,X9] :
    ? [X8] : p(a) ).

fof(s3,axiom,
    ! [X10] :
      ( ~ p(a)
     => ~ r(X10,X10) ) ).

fof(s4,axiom,
    p(f(f(a))) ).

fof(c,conjecture,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
        ( q(f(c))
       => a = a )
    | ! [X26] :
      ? [X27] :
        ( t
        & t ) ) ).

% SZS output end ListOfFormulae
