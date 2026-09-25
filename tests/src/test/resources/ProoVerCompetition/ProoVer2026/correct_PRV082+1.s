%------------------------------------------------------------------------------
% File     : PRV082+1.s : ProoVer 2026
% Proof    : Problems/PRV082+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ~ ! [Y] : p(Y),
    file('Problems/PRV082+1.p',a1) ).

fof(c,conjecture,
    ? [Y] : ~ p(Y),
    file('Problems/PRV082+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [Y] : ~ p(Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ~ p(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,neg]) ).

% SZS output end Proof
