%------------------------------------------------------------------------------
% File     : PRV005+1.s : ProoVer 2026
% Proof    : Problems/PRV005+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] :
      ( s(X,Y)
      & ! [X] : t(X,Y) ),
    file('Problems/PRV005+1.p',a1) ).

fof(c,conjecture,
    ? [X,Y] : s(X,Y),
    file('Problems/PRV005+1.p',c) ).

fof(neg,negated_conjecture,
    ~ ? [X,Y] : s(X,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [X] :
      ( s(X,sK0(X))
      & ! [X1] : t(X1,sK0(X)) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(X))],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[sk,neg]) ).

% SZS output end Proof
