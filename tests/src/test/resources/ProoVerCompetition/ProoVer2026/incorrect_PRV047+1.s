%------------------------------------------------------------------------------
% File     : PRV047+1.s : ProoVer 2026
% Proof    : Problems/PRV047+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(b),
    file('Problems/PRV047+1.p',a1) ).

fof(c,conjecture,
    p(b),
    file('Problems/PRV047+1.p',c) ).

fof(s,plain,
    p(b),
    inference(copy,[status(thm)],[a1]) ).

fof(negc,negated_conjecture,
    ~ p(b),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
