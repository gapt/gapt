%------------------------------------------------------------------------------
% File     : PRV087+1.s : ProoVer 2026
% Proof    : Problems/PRV087+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ( ? [Y] : p(Y)
    & ? [Y] : q(Y) ),
    file('Problems/PRV087+1.p',a1) ).

fof(c,conjecture,
    ( ? [Y] : p(Y)
    & ? [Y] : q(Y) ),
    file('Problems/PRV087+1.p',c) ).

fof(sk,plain,
    ( p(sK0)
    & q(sK0) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(s,plain,
    ( ? [Y] : p(Y)
    & ? [Y] : q(Y) ),
    inference(weaken,[status(thm)],[sk]) ).

fof(negc,negated_conjecture,
    ~ ( ? [Y] : p(Y)
      & ? [Y] : q(Y) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
