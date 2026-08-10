%------------------------------------------------------------------------------
% File     : PRV085+1.s : ProoVer 2026
% Proof    : Problems/PRV085+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y,Z] : r(X,Y,Z),
    file('Problems/PRV085+1.p',a1) ).

fof(c,conjecture,
    ? [X,Y,Z] : r(X,Y,Z),
    file('Problems/PRV085+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Y,Z] : r(X,Y,Z),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [X] :
    ? [Y] : r(X,Y,sK0(X)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Z,sK0(X))],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,neg]) ).

% SZS output end Proof
