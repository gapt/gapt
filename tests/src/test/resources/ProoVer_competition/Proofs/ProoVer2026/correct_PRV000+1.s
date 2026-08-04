%------------------------------------------------------------------------------
% File     : PRV000+1.s : ProoVer 2026
% Proof    : Problems/PRV000+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ? [X] :
    ! [Y] :
    ? [Z] :
    ! [W] : r(X,Y,Z,W),
    file('Problems/PRV000+1.p',a1) ).

fof(c,conjecture,
    ? [X] :
    ! [Y] :
    ? [Z] :
    ! [W] : r(X,Y,Z,W),
    file('Problems/PRV000+1.p',c) ).

fof(neg,negated_conjecture,
    ! [A] :
    ? [B] :
    ! [C] :
    ? [D] : ~ r(A,B,C,D),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,a1]) ).

% SZS output end Proof
