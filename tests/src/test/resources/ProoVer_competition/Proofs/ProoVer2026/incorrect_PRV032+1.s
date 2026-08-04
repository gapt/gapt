%------------------------------------------------------------------------------
% File     : PRV032+1.s : ProoVer 2026
% Proof    : Problems/PRV032+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV032+1.p',a1) ).

fof(a2,axiom,
    ( p(a)
   => q(a) ),
    file('Problems/PRV032+1.p',a2) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV032+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[a1]) ).

fof(s,plain,
    q(a),
    inference(modus_ponens,[status(thm)],[a1,a2]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s]) ).

% SZS output end Proof
