%------------------------------------------------------------------------------
% File     : PRV062+1.s : ProoVer 2026
% Proof    : Problems/PRV062+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p_ef(a),
    file('Problems/PRV062+1.p',a1) ).

fof(a2,axiom,
    ~ p_ef(a),
    file('Problems/PRV062+1.p',a2) ).

fof(a3,axiom,
    q_ef(a),
    file('Problems/PRV062+1.p',a3) ).

fof(b1,axiom,
    ! [X] :
      ( q_ef(X)
     => r_ef(X) ),
    file('Problems/PRV062+1.p',b1) ).

fof(c,conjecture,
    r_ef(a),
    file('Problems/PRV062+1.p',c) ).

fof(s0,negated_conjecture,
    ~ r_ef(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(unused,plain,
    $false,
    inference(ex_falso,[status(thm)],[a1,a2]) ).

fof(s1,plain,
    ( q_ef(a)
   => r_ef(a) ),
    inference(instantiate,[status(thm)],[b1]) ).

fof(s2,plain,
    r_ef(a),
    inference(horn,[status(thm)],[a3,s1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s2]) ).

% SZS output end Proof
