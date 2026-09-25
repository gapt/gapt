%------------------------------------------------------------------------------
% File     : PRV037+1.s : ProoVer 2026
% Proof    : Problems/PRV037+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ~ q(a),
    file('Problems/PRV037+1.p',a1) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV037+1.p',c) ).

fof(neg,negated_conjecture,
    q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[a1,neg]) ).

% SZS output end Proof
