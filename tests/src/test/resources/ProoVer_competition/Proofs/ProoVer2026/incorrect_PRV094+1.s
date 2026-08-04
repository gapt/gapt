%------------------------------------------------------------------------------
% File     : PRV094+1.s : ProoVer 2026
% Proof    : Problems/PRV094+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] : r(X,Y),
    file('Problems/PRV094+1.p',a1) ).

fof(c,conjecture,
    ? [X,Y] : r(X,Y),
    file('Problems/PRV094+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Y] : r(X,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [X] : r(X,sK0(X)),
    inference(skolemize,[status(esa),skolemize(Y,sK0(X))],[a1]) ).

fof(inst,plain,
    r(m0,sK0(m0)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[sk]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,inst]) ).

% SZS output end Proof
