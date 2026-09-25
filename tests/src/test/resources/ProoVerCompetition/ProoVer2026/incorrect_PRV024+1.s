%------------------------------------------------------------------------------
% File     : PRV024+1.s : ProoVer 2026
% Proof    : Problems/PRV024+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV024+1.p',a1) ).

fof(c,conjecture,
    q(a),
    file('Problems/PRV024+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    q(a),
    inference(rewrite,[status(thm)],[s2]) ).

fof(s2,plain,
    q(a),
    inference(rewrite,[status(thm)],[s3]) ).

fof(s3,plain,
    q(a),
    inference(rewrite,[status(thm)],[s4]) ).

fof(s4,plain,
    q(a),
    inference(rewrite,[status(thm)],[s1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s1]) ).

% SZS output end Proof
