%------------------------------------------------------------------------------
% File     : PRV049+1.s : ProoVer 2026
% Proof    : Problems/PRV049+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    q(a),
    file('Problems/PRV049+1.p',a1) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV049+1.p',c) ).

fof(s,plain,
    q(a),
    inference(copy,[status(thm)],[a1]) ).

fof(negc,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
