%------------------------------------------------------------------------------
% File     : PRV021+1.s : ProoVer 2026
% Proof    : Problems/PRV021+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ( p(a)
    | q(f(a)) ),
    file('Problems/PRV021+1.p',a1) ).

fof(a2,axiom,
    ~ p(a),
    file('Problems/PRV021+1.p',a2) ).

fof(a3,axiom,
    f(a) = b,
    file('Problems/PRV021+1.p',a3) ).

fof(c,conjecture,
    q(b),
    file('Problems/PRV021+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(b),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(r1,plain,
    q(f(a)),
    inference(resolution,[status(thm)],[a1,a2]) ).

fof(r2,plain,
    q(b),
    inference(paramodulation,[status(thm)],[r1,a3]) ).

fof(bot,plain,
    $false,
    inference(resolution,[status(thm)],[neg,r2]) ).

% SZS output end Proof
