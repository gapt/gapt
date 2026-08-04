%------------------------------------------------------------------------------
% File     : PRV035+1.s : ProoVer 2026
% Proof    : Problems/PRV035+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV035+1.p',a1) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV035+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(badsk,plain,
    q(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0)],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,badsk]) ).

% SZS output end Proof
