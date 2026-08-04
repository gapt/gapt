%------------------------------------------------------------------------------
% File     : PRV030+1.s : ProoVer 2026
% Proof    : Problems/PRV030+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV030+1.p',a1) ).

fof(a2,axiom,
    ~ p(a),
    file('Problems/PRV030+1.p',a2) ).

fof(c,conjecture,
    q(b),
    file('Problems/PRV030+1.p',c) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[a1,a2]) ).

fof(negc,negated_conjecture,
    ~ q(b),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot2,plain,
    $false,
    inference(consequence,[status(thm)],[negc,bot]) ).

% SZS output end Proof
