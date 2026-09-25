%------------------------------------------------------------------------------
% File     : PRV052+1.s : ProoVer 2026
% Proof    : Problems/PRV052+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    q(b),
    file('Problems/PRV052+1.p',a1) ).

fof(c,conjecture,
    q(b),
    file('Problems/PRV052+1.p',c) ).

fof(s,plain,
    q(b),
    inference(copy,[status(thm)],[a1]) ).

fof(negc,negated_conjecture,
    ~ q(b),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
