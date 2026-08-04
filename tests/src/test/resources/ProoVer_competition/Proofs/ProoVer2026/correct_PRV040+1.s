%------------------------------------------------------------------------------
% File     : PRV040+1.s : ProoVer 2026
% Proof    : Problems/PRV040+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    q(a),
    file('Problems/PRV040+1.p',a1) ).

fof(a2,axiom,
    p(a),
    file('Problems/PRV040+1.p',a2) ).

fof(a3,axiom,
    ~ p(a),
    file('Problems/PRV040+1.p',a3) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV040+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s,plain,
    q(b),
    inference(ex_falso,[status(thm)],[a2,a3]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[a1,neg]) ).

% SZS output end Proof
