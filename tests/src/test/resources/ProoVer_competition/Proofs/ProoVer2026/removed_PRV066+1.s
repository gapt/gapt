%------------------------------------------------------------------------------
% File     : PRV066+1.s : ProoVer 2026
% Proof    : Problems/PRV066+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [U1] :
    ? [V1] :
    ! [U2] :
    ? [V2,Y] : r(U1,V1,Y),
    file('Problems/PRV066+1.p',a1) ).

fof(c,conjecture,
    ? [A,B,C] : r(A,B,C),
    file('Problems/PRV066+1.p',c) ).

fof(neg,negated_conjecture,
    ! [A,B,C] : ~ r(A,B,C),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(sk,plain,
    ! [U1] :
    ? [V1] :
    ! [U2] :
    ? [V2] : r(U1,V1,sK0(U1,U2,V1,V2,a,f(g(U1,U2),g(V1,V2),a))),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(U1,U2,V1,V2,a,f(g(U1,U2),g(V1,V2),a)))],[a1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[neg,sk]) ).

% SZS output end Proof
