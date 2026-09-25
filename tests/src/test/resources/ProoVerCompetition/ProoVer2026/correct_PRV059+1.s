%------------------------------------------------------------------------------
% File     : PRV059+1.s : ProoVer 2026
% Proof    : Problems/PRV059+1.p
% Source   : ProoVer 2026
% Status   : Unknown
% SPC      : FOF_UNK_RFO_NEQ
%------------------------------------------------------------------------------
% SZS output start Proof
fof(a1,axiom,
    ! [X] :
    ? [Y] : relA(X,Y),
    file('Problems/PRV059+1.p',a1) ).

fof(b1,axiom,
    ! [X] :
      ( midA1(X)
     => midA2(X) ),
    file('Problems/PRV059+1.p',b1) ).

fof(b2,axiom,
    ! [X] :
      ( midA2(X)
     => midA3(X) ),
    file('Problems/PRV059+1.p',b2) ).

fof(c,conjecture,
    ? [X,Y] : relA(X,Y),
    file('Problems/PRV059+1.p',c) ).

fof(s0,negated_conjecture,
    ! [X,Y] : ~ relA(X,Y),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(s1,plain,
    ! [X] : relA(X,sK0(X)),
    inference(skolemize,[new_symbols(skolem,[sK0]),skolemize(Y,sK0(X)),status(esa)],[a1]) ).

fof(s2,plain,
    relA(m0,sK0(m0)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s1]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[s0,s2]) ).

% SZS output end Proof
