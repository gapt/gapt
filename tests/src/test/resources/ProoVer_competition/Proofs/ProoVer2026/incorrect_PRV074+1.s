%------------------------------------------------------------------------------
% File     : PRV074+1.s : ProoVer 2026
% Proof    : Problems/PRV074+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] : r(X,Y),
    file('Problems/PRV074+1.p',a1) ).

fof(a2,axiom,
    ! [X] : s(f(X)),
    file('Problems/PRV074+1.p',a2) ).

fof(c,conjecture,
    ? [X,Y] : r(X,Y),
    file('Problems/PRV074+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Y] : r(X,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [X] : r(X,f(X)),
    inference(skolemize,[status(esa),new_symbols(skolem,[f]),skolemize(Y,f(X))],[a1]) ).

fof(inst,plain,
    r(m0,f(m0)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[sk]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,inst]) ).

% SZS output end Proof
