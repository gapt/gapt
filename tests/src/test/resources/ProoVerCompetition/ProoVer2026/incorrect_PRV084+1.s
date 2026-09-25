%------------------------------------------------------------------------------
% File     : PRV084+1.s : ProoVer 2026
% Proof    : Problems/PRV084+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ~ ( p
     => ? [Y] : q(Y) ),
    file('Problems/PRV084+1.p',a1) ).

fof(c,conjecture,
    p,
    file('Problems/PRV084+1.p',c) ).

fof(sk,plain,
    ~ ( p
     => q(sK0) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(s,plain,
    p,
    inference(simplify,[status(thm)],[sk]) ).

fof(negc,negated_conjecture,
    ~ p,
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
