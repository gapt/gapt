%------------------------------------------------------------------------------
% File     : PRV007+1.s : ProoVer 2026
% Proof    : Problems/PRV007+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    p(sk0(m(a))),
    file('Problems/PRV007+1.p',a1) ).

fof(a2,axiom,
    ! [Y] : m(Y) = f(Y),
    file('Problems/PRV007+1.p',a2) ).

fof(a3,axiom,
    ! [X] :
    ? [Y] : d(X,Y),
    file('Problems/PRV007+1.p',a3) ).

fof(c,conjecture,
    ! [Z] : p(sk0(f(Z))),
    file('Problems/PRV007+1.p',c) ).

fof(sk1,plain,
    ! [X] : d(X,sK1(X)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(Y,sK1(X))],[a3]) ).

fof(s2,plain,
    a = a,
    inference(reflexivity,[status(thm)],[a2]) ).

fof(s,plain,
    ! [Z] : p(sk0(f(Z))),
    inference(paramodulation,[status(thm)],[a1,a2]) ).

fof(negc,negated_conjecture,
    ~ ! [Z] : p(sk0(f(Z))),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s]) ).

% SZS output end Proof
