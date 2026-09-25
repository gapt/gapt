%------------------------------------------------------------------------------
% File     : PRV055+1.s : ProoVer 2026
% Proof    : Problems/PRV055+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV055+1.p',a1) ).

fof(c,conjecture,
    p(a),
    file('Problems/PRV055+1.p',c) ).

fof(neg,negated_conjecture,
    ~ p(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,a1]) ).

% SZS output end Proof
