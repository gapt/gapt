%------------------------------------------------------------------------------
% File     : PRV061+1.s : ProoVer 2026
% Proof    : Problems/PRV061+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p_dup(a),
    file('Problems/PRV061+1.p',a1) ).

fof(ax1,axiom,
    p_dup(a),
    file('Problems/PRV061+1.p',a1) ).

fof(ax2,axiom,
    p_dup(a),
    file('Problems/PRV061+1.p',a1) ).

fof(b1,axiom,
    ! [X] :
      ( p_dup(X)
     => q_dup(X) ),
    file('Problems/PRV061+1.p',b1) ).

fof(b2,axiom,
    ! [X] :
      ( q_dup(X)
     => r_dup(X) ),
    file('Problems/PRV061+1.p',b2) ).

fof(c,conjecture,
    r_dup(a),
    file('Problems/PRV061+1.p',c) ).

fof(s0,negated_conjecture,
    ~ r_dup(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ( p_dup(a)
   => q_dup(a) ),
    inference(instantiate,[status(thm)],[b1]) ).

fof(s2,plain,
    q_dup(a),
    inference(horn,[status(thm)],[ax1,s1]) ).

fof(s3,plain,
    ( q_dup(a)
   => r_dup(a) ),
    inference(instantiate,[status(thm)],[b2]) ).

fof(s4,plain,
    r_dup(a),
    inference(horn,[status(thm)],[s2,s3]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,ax2,s4]) ).

% SZS output end Proof
