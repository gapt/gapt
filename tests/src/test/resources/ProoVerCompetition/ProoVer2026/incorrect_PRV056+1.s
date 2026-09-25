%------------------------------------------------------------------------------
% File     : PRV056+1.s : ProoVer 2026
% Proof    : Problems/PRV056+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X,Z] :
    ? [Y] : rel16(X,Z,Y),
    file('Problems/PRV056+1.p',a1) ).

fof(c,conjecture,
    ? [X,Z,Y] : rel16(X,Z,Y),
    file('Problems/PRV056+1.p',c) ).

fof(s0,negated_conjecture,
    ! [X,Z,Y] : ~ rel16(X,Z,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ! [X,Z] : rel16(X,Z,sK0(X,Z)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(X,Z))],[a1]) ).

fof(s2,plain,
    rel16(m0,n0,sK0(n0,m0)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0,n0])],[s1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s2]) ).

% SZS output end Proof
