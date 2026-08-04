%------------------------------------------------------------------------------
% File     : PRV017+1.s : ProoVer 2026
% Proof    : Problems/PRV017+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
      ( greek(X)
     => human(X) ),
    file('Problems/PRV017+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( human(X)
     => ( mortal(X)
        | immortal(X) ) ),
    file('Problems/PRV017+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( immortal(X)
     => god(X) ),
    file('Problems/PRV017+1.p',a3) ).

fof(a4,axiom,
    greek(socrates),
    file('Problems/PRV017+1.p',a4) ).

fof(a5,axiom,
    ~ god(socrates),
    file('Problems/PRV017+1.p',a5) ).

fof(c,conjecture,
    mortal(socrates),
    file('Problems/PRV017+1.p',c) ).

fof(neg,negated_conjecture,
    ~ mortal(socrates),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    human(socrates),
    inference(instantiate_mp,[status(thm)],[a1,a4]) ).

fof(s2,plain,
    ( mortal(socrates)
    | immortal(socrates) ),
    inference(instantiate_mp,[status(thm)],[a2,s1]) ).

fof(s3,plain,
    ~ immortal(socrates),
    inference(contrapositive,[status(thm)],[a3,a5]) ).

fof(s4,plain,
    mortal(socrates),
    inference(disjunctive_syllogism,[status(thm)],[s2,s3]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s4]) ).

% SZS output end Proof
