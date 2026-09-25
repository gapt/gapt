%------------------------------------------------------------------------------
% File     : PRV009+1.s : ProoVer 2026
% Proof    : Problems/PRV009+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [Z] : ~ q(Z),
    file('Problems/PRV009+1.p',a1) ).

fof(c,conjecture,
    ! [X] :
    ? [Y] :
    ! [Z] :
      ( ( p(X)
      <~> r(Y,Z) )
     <= q(Z) ),
    file('Problems/PRV009+1.p',c) ).

fof(neg,negated_conjecture,
    ? [X] :
    ! [Y,Z] :
      ~ ( ( p(X)
        <~> r(Y,Z) )
       <= q(Z) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [Y,Z] :
      ~ ( ( p(sK0)
        <~> r(Y,Z) )
       <= q(Z) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X,sK0)],[neg]) ).

fof(s1,plain,
    ! [W] : ~ q(W),
    inference(rename_variable,[status(thm)],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s1,sk]) ).

% SZS output end Proof
