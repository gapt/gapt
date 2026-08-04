%------------------------------------------------------------------------------
% File     : PRV002+1.s : ProoVer 2026
% Proof    : Problems/PRV002+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ~ ! [X] :
      ? [Y] :
      ! [Z] :
        ( p(X,Y,Z)
        | ? [X] :
          ! [W] :
            ( q(X,Y,Z,W)
            & ? [Y] : r(X,Y,Z,W) ) ),
    file('Problems/PRV002+1.p',a1) ).

fof(c,conjecture,
    ~ ! [X] :
      ? [Y] :
      ! [Z] :
        ( p(X,Y,Z)
        | ? [X] :
          ! [W] :
            ( q(X,Y,Z,W)
            & ? [Y] : r(X,Y,Z,W) ) ),
    file('Problems/PRV002+1.p',c) ).

fof(neg,negated_conjecture,
    ! [A] :
    ? [B] :
    ! [C] :
      ( p(A,B,C)
      | ? [E] :
        ! [F] :
          ( q(E,B,C,F)
          & ? [G] : r(E,G,F,C) ) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,a1]) ).

% SZS output end Proof
