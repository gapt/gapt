%------------------------------------------------------------------------------
% File     : PRV045+1.s : ProoVer 2026
% Proof    : Problems/PRV045+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(ax1,axiom,
    p(a),
    file('Problems/PRV045+1.p',a1) ).

fof(ax2,axiom,
    p(a),
    file('Problems/PRV045+1.p',a1) ).

fof(c,conjecture,
    p(a),
    file('Problems/PRV045+1.p',c) ).

fof(neg,negated_conjecture,
    ~ p(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,ax1]) ).

% SZS output end Proof
