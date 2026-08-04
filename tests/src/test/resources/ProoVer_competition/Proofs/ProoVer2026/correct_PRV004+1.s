%------------------------------------------------------------------------------
% File     : PRV004+1.s : ProoVer 2026
% Proof    : Problems/PRV004+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X,Z] :
    ? [Y] :
    ! [W] : r(X,Z,Y,W),
    file('Problems/PRV004+1.p',a1) ).

fof(c,conjecture,
    ? [X,Z,Y,W] : r(X,Z,Y,W),
    file('Problems/PRV004+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Z,Y,W] : r(X,Z,Y,W),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [A,B,C] : r(A,B,sK0(A,B),C),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(X,Z))],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,neg]) ).

% SZS output end Proof
