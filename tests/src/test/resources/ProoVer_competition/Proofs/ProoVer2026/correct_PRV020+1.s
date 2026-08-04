%------------------------------------------------------------------------------
% File     : PRV020+1.s : ProoVer 2026
% Proof    : Problems/PRV020+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
      ( p(X)
      | q(X) ),
    file('Problems/PRV020+1.p',a1) ).

fof(a2,axiom,
    ! [X] :
      ( ~ p(X)
      | s(X) ),
    file('Problems/PRV020+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
      ( ~ q(X)
      | s(X) ),
    file('Problems/PRV020+1.p',a3) ).

fof(c,conjecture,
    ! [X] : s(X),
    file('Problems/PRV020+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ! [X] : s(X),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ~ s(sK0),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X,sK0)],[neg]) ).

fof(r1,plain,
    ! [X] :
      ( q(X)
      | s(X) ),
    inference(resolution,[status(thm)],[a1,a2]) ).

fof(r2,plain,
    ! [X] : s(X),
    inference(resolution,[status(thm)],[r1,a3]) ).

fof(bot,plain,
    $false,
    inference(resolution,[status(thm)],[r2,sk]) ).

% SZS output end Proof
