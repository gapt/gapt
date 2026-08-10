%------------------------------------------------------------------------------
% File     : PRV098+1.s : ProoVer 2026
% Proof    : Problems/PRV098+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV098+1.p',a1) ).

fof(c,conjecture,
    p(a),
    file('Problems/PRV098+1.p',c) ).

fof(l0,plain,
    p(a),
    inference(copy,[status(thm)],[a1]) ).

fof(l1,plain,
    p(a),
    inference(duplicate,[status(thm)],[l0,l0]) ).

fof(l2,plain,
    p(a),
    inference(duplicate,[status(thm)],[l1,l1]) ).

fof(l3,plain,
    p(a),
    inference(duplicate,[status(thm)],[l2,l2]) ).

fof(l4,plain,
    p(a),
    inference(duplicate,[status(thm)],[l3,l3]) ).

fof(l5,plain,
    p(a),
    inference(duplicate,[status(thm)],[l4,l4]) ).

fof(l6,plain,
    p(a),
    inference(duplicate,[status(thm)],[l5,l5]) ).

fof(l7,plain,
    p(a),
    inference(duplicate,[status(thm)],[l6,l6]) ).

fof(l8,plain,
    p(a),
    inference(duplicate,[status(thm)],[l7,l7]) ).

fof(l9,plain,
    p(a),
    inference(duplicate,[status(thm)],[l8,l8]) ).

fof(l10,plain,
    p(a),
    inference(duplicate,[status(thm)],[l9,l9]) ).

fof(l11,plain,
    p(a),
    inference(duplicate,[status(thm)],[l10,l10]) ).

fof(l12,plain,
    p(a),
    inference(duplicate,[status(thm)],[l11,l11]) ).

fof(l13,plain,
    p(a),
    inference(duplicate,[status(thm)],[l12,l12]) ).

fof(l14,plain,
    p(a),
    inference(duplicate,[status(thm)],[l13,l13]) ).

fof(l15,plain,
    p(a),
    inference(duplicate,[status(thm)],[l14,l14]) ).

fof(l16,plain,
    p(a),
    inference(duplicate,[status(thm)],[l15,l15]) ).

fof(l17,plain,
    p(a),
    inference(duplicate,[status(thm)],[l16,l16]) ).

fof(l18,plain,
    p(a),
    inference(duplicate,[status(thm)],[l17,l17]) ).

fof(l19,plain,
    p(a),
    inference(duplicate,[status(thm)],[l18,l18]) ).

fof(l20,plain,
    p(a),
    inference(duplicate,[status(thm)],[l19,l19]) ).

fof(l21,plain,
    p(a),
    inference(duplicate,[status(thm)],[l20,l20]) ).

fof(l22,plain,
    p(a),
    inference(duplicate,[status(thm)],[l21,l21]) ).

fof(l23,plain,
    p(a),
    inference(duplicate,[status(thm)],[l22,l22]) ).

fof(l24,plain,
    p(a),
    inference(duplicate,[status(thm)],[l23,l23]) ).

fof(l25,plain,
    p(a),
    inference(duplicate,[status(thm)],[l24,l24]) ).

fof(l26,plain,
    p(a),
    inference(duplicate,[status(thm)],[l25,l25]) ).

fof(l27,plain,
    p(a),
    inference(duplicate,[status(thm)],[l26,l26]) ).

fof(l28,plain,
    p(a),
    inference(duplicate,[status(thm)],[l27,l27]) ).

fof(l29,plain,
    p(a),
    inference(duplicate,[status(thm)],[l28,l28]) ).

fof(l30,plain,
    p(a),
    inference(duplicate,[status(thm)],[l29,l29]) ).

fof(negc,negated_conjecture,
    ~ p(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,l30]) ).

% SZS output end Proof
