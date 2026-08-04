%------------------------------------------------------------------------------
% File     : PRV018+1.s : ProoVer 2026
% Proof    : Problems/PRV018+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    a = b,
    file('Problems/PRV018+1.p',a1) ).

fof(a2,axiom,
    b = c,
    file('Problems/PRV018+1.p',a2) ).

fof(a3,axiom,
    h(a) = d,
    file('Problems/PRV018+1.p',a3) ).

fof(a4,axiom,
    ! [X] :
      ( p(X)
     => q(h(X)) ),
    file('Problems/PRV018+1.p',a4) ).

fof(a5,axiom,
    p(c),
    file('Problems/PRV018+1.p',a5) ).

fof(c,conjecture,
    q(d),
    file('Problems/PRV018+1.p',c) ).

fof(neg,negated_conjecture,
    ~ q(d),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    a = c,
    inference(transitivity,[status(thm)],[a1,a2]) ).

fof(s2,plain,
    p(a),
    inference(paramodulation,[status(thm)],[a5,s1]) ).

fof(s3,plain,
    q(h(a)),
    inference(instantiate_mp,[status(thm)],[a4,s2]) ).

fof(s4,plain,
    q(d),
    inference(paramodulation,[status(thm)],[s3,a3]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,s4]) ).

% SZS output end Proof
