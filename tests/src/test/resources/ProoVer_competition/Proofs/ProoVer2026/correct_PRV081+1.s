%------------------------------------------------------------------------------
% File     : PRV081+1.s : ProoVer 2026
% Proof    : Problems/PRV081+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X,Z] :
    ? [Y] : r(X,Z,Y),
    file('Problems/PRV081+1.p',a1) ).

fof(c,conjecture,
    ? [X,Z,Y] : r(X,Z,Y),
    file('Problems/PRV081+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Z,Y] : r(X,Z,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [X,Z] : r(X,Z,sK0(Z,X)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(Z,X))],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,neg]) ).

% SZS output end Proof
