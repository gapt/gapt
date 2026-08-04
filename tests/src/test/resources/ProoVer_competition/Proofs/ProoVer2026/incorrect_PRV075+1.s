%------------------------------------------------------------------------------
% File     : PRV075+1.s : ProoVer 2026
% Proof    : Problems/PRV075+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ? [Y] : p(Y),
    file('Problems/PRV075+1.p',a1) ).

fof(a2,axiom,
    ? [Z] : q(Z),
    file('Problems/PRV075+1.p',a2) ).

fof(c,conjecture,
    ? [W] :
      ( p(W)
      & q(W) ),
    file('Problems/PRV075+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [W] :
        ( p(W)
        & q(W) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk1,plain,
    p(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(sk2,plain,
    q(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Z,sK0)],[a2]) ).

fof(s,plain,
    ( p(sK0)
    & q(sK0) ),
    inference(conjunction,[status(thm)],[sk1,sk2]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s]) ).

% SZS output end Proof
