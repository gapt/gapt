%------------------------------------------------------------------------------
% File     : PRV022+1.s : ProoVer 2026
% Proof    : Problems/PRV022+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(c,conjecture,
    ( ? [X] :
      ! [Y] : r(X,Y)
   => ! [Y] :
      ? [X] : r(X,Y) ),
    file('Problems/PRV022+1.p',c) ).

fof(neg,negated_conjecture,
    ( ? [X] :
      ! [Y] : r(X,Y)
    & ? [Y] :
      ! [X] : ~ r(X,Y) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ? [X] :
    ! [Y] : r(X,Y),
    inference(alpha,[status(thm)],[neg]) ).

fof(s2,plain,
    ? [Y] :
    ! [X] : ~ r(X,Y),
    inference(alpha,[status(thm)],[neg]) ).

fof(sk1,plain,
    ! [Y] : r(sK0,Y),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X,sK0)],[s1]) ).

fof(sk2,plain,
    ! [X] : ~ r(X,sK1),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(Y,sK1)],[s2]) ).

fof(s3,plain,
    r(sK0,sK1),
    inference(instantiate,[status(thm)],[sk1]) ).

fof(s4,plain,
    ~ r(sK0,sK1),
    inference(instantiate,[status(thm)],[sk2]) ).

fof(bot,plain,
    $false,
    inference(resolution,[status(thm)],[s3,s4]) ).

% SZS output end Proof
