%------------------------------------------------------------------------------
% File     : PRV008+1.s : ProoVer 2026
% Proof    : Problems/PRV008+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] :
      ( s(X,Y)
      & ! [X] : t(X,Y) ),
    file('Problems/PRV008+1.p',a1) ).

fof(a4,axiom,
    ! [U] :
    ? [Vv] : w(U,Vv),
    file('Problems/PRV008+1.p',a4) ).

fof(c,conjecture,
    ? [U,Vv] : s(U,Vv),
    file('Problems/PRV008+1.p',c) ).

fof(s0,plain,
    ! [X2] :
    ? [Y2] :
      ( s(X2,Y2)
      & ! [X3] : t(X3,Y2) ),
    inference(rename_variable,[status(thm)],[a1]) ).

fof(skv,plain,
    ! [U] : w(U,sK9(U)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK9]),skolemize(Vv,sK9(U))],[a4]) ).

fof(sk,plain,
    ! [X] :
      ( s(X,sK0(X))
      & ! [X] : t(X,sK0(X)) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(X))],[a1]) ).

fof(s2,plain,
    ( s(a,sK0(a))
    & ! [X] : t(X,sK0(X)) ),
    inference(instantiate,[status(thm)],[sk]) ).

fof(s3,plain,
    ? [U,Vv] : s(U,Vv),
    inference(existential_gen,[status(thm)],[s2]) ).

fof(negc,negated_conjecture,
    ~ ? [U,Vv] : s(U,Vv),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s3]) ).

% SZS output end Proof
