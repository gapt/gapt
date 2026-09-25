%------------------------------------------------------------------------------
% File     : PRV028+1.s : ProoVer 2026
% Proof    : Problems/PRV028+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ( p(a)
   => q(a) ),
    file('Problems/PRV028+1.p',a1) ).

fof(a2,axiom,
    p(a),
    file('Problems/PRV028+1.p',a2) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV028+1.p',c) ).

fof(s,plain,
    p(a),
    inference(copy,[status(thm)],[a2]) ).

fof(negc,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
