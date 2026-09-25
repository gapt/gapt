%------------------------------------------------------------------------------
% File     : PRV031+1.s : ProoVer 2026
% Proof    : Problems/PRV031+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV031+1.p',a1) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV031+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s,plain,
    q(a),
    inference(assume,[status(thm)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s]) ).

% SZS output end Proof
