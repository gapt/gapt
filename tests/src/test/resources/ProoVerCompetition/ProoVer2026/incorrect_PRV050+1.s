%------------------------------------------------------------------------------
% File     : PRV050+1.s : ProoVer 2026
% Proof    : Problems/PRV050+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV050+1.p',a1) ).

fof(c,conjecture,
    p(a),
    file('Problems/PRV050+1.p',c) ).

fof(s,plain,
    p(a),
    inference(copy,[status(thm)],[a1]) ).

fof(negc,negated_conjecture,
    ~ p(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
