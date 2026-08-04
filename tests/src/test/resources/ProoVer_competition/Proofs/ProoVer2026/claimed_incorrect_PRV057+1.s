%------------------------------------------------------------------------------
% File     : PRV057+1.s : ProoVer 2026
% Proof    : Problems/PRV057+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a0,axiom,
    p1_cs(a),
    file('Problems/PRV057+1.p',a0) ).

fof(a1,axiom,
    ! [X] :
      ( p1_cs(X)
     => p2_cs(X) ),
    file('Problems/PRV057+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( p2_cs(X)
     => p3_cs(X) ),
    file('Problems/PRV057+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( p3_cs(X)
     => p4_cs(X) ),
    file('Problems/PRV057+1.p',a3) ).

fof(a4,axiom,
    ! [X] :
      ( p4_cs(X)
     => p5_cs(X) ),
    file('Problems/PRV057+1.p',a4) ).

fof(a5,axiom,
    ! [X] :
      ( p5_cs(X)
     => p6_cs(X) ),
    file('Problems/PRV057+1.p',a5) ).

fof(c,conjecture,
    p6_cs(a),
    file('Problems/PRV057+1.p',c) ).

fof(s0,negated_conjecture,
    ~ p6_cs(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ( p1_cs(a)
   => p2_cs(a) ),
    inference(instantiate,[status(thm)],[a1]) ).

fof(s2,plain,
    ( p2_cs(a)
   => p3_cs(a) ),
    inference(instantiate,[status(thm)],[a2]) ).

fof(s3,plain,
    ( p3_cs(a)
   => p4_cs(a) ),
    inference(instantiate,[status(thm)],[a3]) ).

fof(s4,plain,
    ( p4_cs(a)
   => p5_cs(a) ),
    inference(instantiate,[status(thm)],[a4]) ).

fof(s5,plain,
    ( p5_cs(a)
   => p6_cs(a) ),
    inference(instantiate,[status(thm)],[a5]) ).

fof(s6,plain,
    p6_cs(a),
    inference(horn,[status(thm)],[a0,s1,s2,s3,s4,s5]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[S0,s6]) ).

% SZS output end Proof
