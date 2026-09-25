%------------------------------------------------------------------------------
% File     : PRV019+1.s : ProoVer 2026
% Proof    : Problems/PRV019+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
      ( p(X)
      | q(X) ),
    file('Problems/PRV019+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( p(X)
     => r(X) ),
    file('Problems/PRV019+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( q(X)
     => r(X) ),
    file('Problems/PRV019+1.p',a3) ).

fof(c,conjecture,
    ! [X] : r(X),
    file('Problems/PRV019+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ! [X] : r(X),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ~ r(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X,sK0)],[neg]) ).

fof(s1,plain,
    ( p(sK0)
    | q(sK0) ),
    inference(instantiate,[status(thm)],[a1]) ).

fof(s2,plain,
    r(sK0),
    inference(case_analysis,[status(thm)],[s1,a2,a3]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,s2]) ).

% SZS output end Proof
