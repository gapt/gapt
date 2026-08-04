%------------------------------------------------------------------------------
% File     : PRV096+1.s : ProoVer 2026
% Proof    : Problems/PRV096+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ? [Y] : p(a),
    file('Problems/PRV096+1.p',a1) ).

fof(c,conjecture,
    ? [Z] : p(Z),
    file('Problems/PRV096+1.p',c) ).

fof(sk,plain,
    p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(s,plain,
    ? [Z] : p(Z),
    inference(existential_gen,[status(thm)],[sk]) ).

fof(negc,negated_conjecture,
    ~ ? [Z] : p(Z),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
