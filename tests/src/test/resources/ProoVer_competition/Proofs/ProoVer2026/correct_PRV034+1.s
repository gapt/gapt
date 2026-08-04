%------------------------------------------------------------------------------
% File     : PRV034+1.s : ProoVer 2026
% Proof    : Problems/PRV034+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(a),
    file('Problems/PRV034+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( p(X)
     => q(X) ),
    file('Problems/PRV034+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( p(X)
     => r(X) ),
    file('Problems/PRV034+1.p',a3) ).

fof(c,conjecture,
    ( q(a)
    & r(a) ),
    file('Problems/PRV034+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ( q(a)
      & r(a) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(lemma,plain,
    p(a),
    inference(copy,[status(thm)],[a1]) ).

fof(s1,plain,
    q(a),
    inference(modus_ponens,[status(thm)],[a2,lemma]) ).

fof(s2,plain,
    r(a),
    inference(modus_ponens,[status(thm)],[a3,lemma]) ).

fof(s3,plain,
    ( q(a)
    & r(a) ),
    inference(conjunction,[status(thm)],[s1,s2]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s3]) ).

% SZS output end Proof
