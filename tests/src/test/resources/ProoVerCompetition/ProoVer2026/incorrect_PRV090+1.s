%------------------------------------------------------------------------------
% File     : PRV090+1.s : ProoVer 2026
% Proof    : Problems/PRV090+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ? [Y] : p(Y),
    file('Problems/PRV090+1.p',a1) ).

fof(a2,axiom,
    ? [W] : q(W),
    file('Problems/PRV090+1.p',a2) ).

fof(c,conjecture,
    ? [Z] :
      ( p(Z)
      & q(Z) ),
    file('Problems/PRV090+1.p',c) ).

fof(skA,plain,
    p(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(skB,plain,
    q(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(W,sK0)],[a2]) ).

fof(s,plain,
    ( p(sK0)
    & q(sK0) ),
    inference(conjunction,[status(thm)],[skA,skB]) ).

fof(s2,plain,
    ? [Z] :
      ( p(Z)
      & q(Z) ),
    inference(existential_gen,[status(thm)],[s]) ).

fof(negc,negated_conjecture,
    ~ ? [Z] :
        ( p(Z)
        & q(Z) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s2]) ).

% SZS output end Proof
