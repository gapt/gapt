%------------------------------------------------------------------------------
% File     : PRV048+1.s : ProoVer 2026
% Proof    : Problems/PRV048+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [Y] : p(Y),
    file('Problems/PRV048+1.p',a1) ).

fof(c,conjecture,
    p(a),
    file('Problems/PRV048+1.p',c) ).

fof(neg,negated_conjecture,
    ~ p(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s,plain,
    p(a),
    inference(instantiate,[status(thm)],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s]) ).

% SZS output end Proof
