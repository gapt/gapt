%------------------------------------------------------------------------------
% File     : PRV060+1.s : ProoVer 2026
% Proof    : Problems/PRV060+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] : relB(X,Y),
    file('Problems/PRV060+1.p',a1) ).

fof(b1,axiom,
    ! [X] :
      ( midB1(X)
     => midB2(X) ),
    file('Problems/PRV060+1.p',b1) ).

fof(b2,axiom,
    ! [X] :
      ( midB2(X)
     => midB3(X) ),
    file('Problems/PRV060+1.p',b2) ).

fof(c,conjecture,
    ? [X,Y] : relB(X,Y),
    file('Problems/PRV060+1.p',c) ).

fof(s0,negated_conjecture,
    ! [X,Y] : ~ relB(X,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ! [X] : relB(X,sK0(X)),
    inference(skolemize,[status(esa),status(esa),new_symbols(skolem,[sK0]),skolemize(Y,sK0(X))],[a1]) ).

fof(s2,plain,
    relB(m0,sK0(m0)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s2]) ).

% SZS output end Proof
