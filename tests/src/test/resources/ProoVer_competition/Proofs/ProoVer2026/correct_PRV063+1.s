%------------------------------------------------------------------------------
% File     : PRV063+1.s : ProoVer 2026
% Proof    : Problems/PRV063+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s6]) ).

fof(s6,plain,
    p6_topo(a),
    inference(horn,[status(thm)],[a0,s1,s2,s3,s4,s5]) ).

fof(s5,plain,
    ( p5_topo(a)
   => p6_topo(a) ),
    inference(instantiate,[status(thm)],[a5]) ).

fof(s4,plain,
    ( p4_topo(a)
   => p5_topo(a) ),
    inference(instantiate,[status(thm)],[a4]) ).

fof(s3,plain,
    ( p3_topo(a)
   => p4_topo(a) ),
    inference(instantiate,[status(thm)],[a3]) ).

fof(s2,plain,
    ( p2_topo(a)
   => p3_topo(a) ),
    inference(instantiate,[status(thm)],[a2]) ).

fof(s1,plain,
    ( p1_topo(a)
   => p2_topo(a) ),
    inference(instantiate,[status(thm)],[a1]) ).

fof(s0,negated_conjecture,
    ~ p6_topo(a),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(c,conjecture,
    p6_topo(a),
    file('Problems/PRV063+1.p',c) ).

fof(a5,axiom,
    ! [X] :
      ( p5_topo(X)
     => p6_topo(X) ),
    file('Problems/PRV063+1.p',a5) ).

fof(a4,axiom,
    ! [X] :
      ( p4_topo(X)
     => p5_topo(X) ),
    file('Problems/PRV063+1.p',a4) ).

fof(a3,axiom,
    ! [X] :
      ( p3_topo(X)
     => p4_topo(X) ),
    file('Problems/PRV063+1.p',a3) ).

fof(a2,axiom,
    ! [X] :
      ( p2_topo(X)
     => p3_topo(X) ),
    file('Problems/PRV063+1.p',a2) ).

fof(a1,axiom,
    ! [X] :
      ( p1_topo(X)
     => p2_topo(X) ),
    file('Problems/PRV063+1.p',a1) ).

fof(a0,axiom,
    p1_topo(a),
    file('Problems/PRV063+1.p',a0) ).

% SZS output end Proof
