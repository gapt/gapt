%------------------------------------------------------------------------------
% File     : PRV051+1.s : ProoVer 2026
% Proof    : Problems/PRV051+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(ax,axiom,
    q(a),
    file('Problems/PRV051+1.p',c) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV051+1.p',c) ).

fof(s,plain,
    q(a),
    inference(copy,[status(thm)],[ax]) ).

fof(negc,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
