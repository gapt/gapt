%------------------------------------------------------------------------------
% File     : PRV070+1.s : ProoVer 2026
% Proof    : Problems/PRV070+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    a = b,
    file('Problems/PRV070+1.p',a1) ).

fof(a2,axiom,
    p(a),
    file('Problems/PRV070+1.p',a2) ).

fof(c,conjecture,
    p(b),
    file('Problems/PRV070+1.p',c) ).

fof(neg,negated_conjecture,
    ~ p(b),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s,plain,
    p(b),
    inference(paramodulation,[status(thm)],[a1,a2]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s]) ).

% SZS output end Proof
