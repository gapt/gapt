%------------------------------------------------------------------------------
% File     : PRV067+1.s : ProoVer 2026
% Proof    : Problems/PRV067+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
      ( p(X)
      | r(X) ),
    file('Problems/PRV067+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( ~ p(X)
      | t(X) ),
    file('Problems/PRV067+1.p',a2) ).

fof(c,conjecture,
    ( r(a)
    | t(b) ),
    file('Problems/PRV067+1.p',c) ).

fof(s,plain,
    ( r(a)
    | t(b) ),
    inference(resolution,[status(thm)],[a1,a2]) ).

fof(negc,negated_conjecture,
    ~ ( r(a)
      | t(b) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
