%------------------------------------------------------------------------------
% File     : PRV064+1.s : ProoVer 2026
% Proof    : Problems/PRV064+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
      ( man(X)
     => mortal(X) ),
    file('Problems/PRV064+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( mortal(X)
     => dies(X) ),
    file('Problems/PRV064+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( dies(X)
     => finite_life(X) ),
    file('Problems/PRV064+1.p',a3) ).

fof(a4,axiom,
    ! [X] :
      ( finite_life(X)
     => ~ eternal(X) ),
    file('Problems/PRV064+1.p',a4) ).

fof(a5,axiom,
    man(socrates),
    file('Problems/PRV064+1.p',a5) ).

fof(c,conjecture,
    ~ eternal(socrates),
    file('Problems/PRV064+1.p',c) ).

fof(s0,negated_conjecture,
    eternal(socrates),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ( man(socrates)
   => mortal(socrates) ),
    inference(instantiate,[status(thm)],[a1]) ).

fof(s2,plain,
    mortal(socrates),
    inference(horn,[status(thm)],[a5,s1]) ).

fof(s3,plain,
    ( mortal(socrates)
   => dies(socrates) ),
    inference(instantiate,[status(thm)],[a2]) ).

fof(s4,plain,
    dies(socrates),
    inference(horn,[status(thm)],[s2,s3]) ).

fof(s5,plain,
    ( dies(socrates)
   => finite_life(socrates) ),
    inference(instantiate,[status(thm)],[a3]) ).

fof(s6,plain,
    finite_life(socrates),
    inference(horn,[status(thm)],[s4,s5]) ).

fof(s7,plain,
    ( finite_life(socrates)
   => ~ eternal(socrates) ),
    inference(instantiate,[status(thm)],[a4]) ).

fof(s8,plain,
    ~ eternal(socrates),
    inference(horn,[status(thm)],[s6,s7]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s8]) ).

% SZS output end Proof
