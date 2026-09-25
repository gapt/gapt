%------------------------------------------------------------------------------
% File     : PRV016+1.s : ProoVer 2026
% Proof    : Problems/PRV016+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] :
      ( t
      & r(X1,X1) ),
    file('Problems/PRV016+1.p',s0) ).

fof(s1,axiom,
    ! [X3,X4] : p(b),
    file('Problems/PRV016+1.p',s1) ).

fof(s2,axiom,
    ! [X5,X7] :
    ? [X6] :
    ! [X8] : r(X7,b),
    file('Problems/PRV016+1.p',s2) ).

fof(s3,axiom,
    ! [X9] :
    ? [X10] : t,
    file('Problems/PRV016+1.p',s3) ).

fof(s4,axiom,
    ! [X11] :
    ? [X12] : r(f(g(X11,a)),f(f(c))),
    file('Problems/PRV016+1.p',s4) ).

fof(s5,axiom,
    r(a,b),
    file('Problems/PRV016+1.p',s5) ).

fof(c,conjecture,
    ( ? [X36] :
      ! [X8] : r(X36,X36)
    | ! [X39] :
      ? [X40,X41] : q(X39) ),
    file('Problems/PRV016+1.p',c) ).

fof(s6,plain,
    ! [X2] :
    ? [X1] :
      ( t
      & r(X1,X1) ),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s0]) ).

fof(s7,plain,
    ? [X13] :
    ! [X5,X7] :
    ? [X6] :
    ! [X8] : r(X7,X13),
    inference(existential_gen,[status(thm)],[s2]) ).

fof(s8,plain,
    ( ( ( q(g(a,b))
        | r(a,g(c,a)) )
    <=> ! [X14] :
        ? [X15] : q(g(a,a)) )
   => ! [X0,X2] :
      ? [X1] :
        ( t
        & r(X1,X1) ) ),
    inference(add_hypothesis,[status(thm)],[s0]) ).

fof(s9,plain,
    ( ! [X16] :
        ( r(a,a)
        & f(a) = X16 )
    | ~ ! [X16] :
          ( r(a,a)
          & f(a) = X16 ) ),
    inference(excluded_middle,[status(thm)],[s8]) ).

fof(s10,plain,
    ! [X5,X7,X8] : r(X7,b),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X6,sK0(X5,X7))],[s2]) ).

fof(s11,plain,
    ( ! [X5,X7,X8] : r(X7,b)
    & ! [X9] :
      ? [X10] : t ),
    inference(conjunction,[status(thm)],[s10,s3]) ).

fof(s12,plain,
    ! [X9] :
    ? [X10] : t,
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s13,plain,
    ( ~ ! [X16] :
          ( r(a,a)
          & f(a) = X16 )
    | ! [X16] :
        ( r(a,a)
        & f(a) = X16 ) ),
    inference(commute,[status(thm)],[s9]) ).

fof(s14,plain,
    ! [X17,X7] :
    ? [X6] :
    ! [X8] : r(X7,b),
    inference(rename_variable,[status(thm)],[s2]) ).

fof(s15,plain,
    ! [X7,X8] : r(X7,b),
    inference(instantiate,[status(thm)],[s10]) ).

fof(s16,plain,
    ( ! [X11] :
      ? [X12] : r(f(g(X11,a)),f(f(c)))
    | ( ! [X18] :
        ? [X19] : b = f(a)
      & ? [X20] : r(a,g(a,X20)) ) ),
    inference(weaken,[status(thm)],[s4]) ).

fof(s17,plain,
    ? [X21] :
    ! [X5,X7,X8] : r(X7,X21),
    inference(existential_gen,[status(thm)],[s10]) ).

fof(s18,plain,
    ! [X4] : p(b),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m1])],[s1]) ).

fof(s19,plain,
    ? [X22] :
    ! [X3,X4] : p(X22),
    inference(existential_gen,[status(thm)],[s1]) ).

fof(s20,plain,
    ? [X10] : t,
    inference(instantiate,[status(thm),new_symbols(herbrand,[m2])],[s3]) ).

fof(s21,plain,
    ( q(a)
    | ~ q(a) ),
    inference(excluded_middle,[status(thm)],[s11]) ).

fof(s22,plain,
    ? [X23] :
    ! [X17,X7] :
    ? [X6] :
    ! [X8] : r(X7,X23),
    inference(existential_gen,[status(thm)],[s14]) ).

fof(s23,plain,
    ! [X5,X7,X8] : r(X7,b),
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s24,plain,
    c = c,
    inference(reflexivity,[status(thm)],[s23]) ).

fof(s25,plain,
    ! [X9] :
    ? [X10] : t,
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s26,plain,
    ? [X24] :
      ( ( ( q(g(a,b))
          | r(a,g(X24,a)) )
      <=> ! [X14] :
          ? [X15] : q(g(a,a)) )
     => ! [X0,X2] :
        ? [X1] :
          ( t
          & r(X1,X1) ) ),
    inference(existential_gen,[status(thm)],[s8]) ).

fof(s27,plain,
    ( q(a)
    | ~ q(a)
    | ! [X25,X26] :
      ? [X27] : r(c,g(X25,X26)) ),
    inference(weaken,[status(thm)],[s21]) ).

fof(s28,plain,
    ! [X28,X7,X8] : r(X7,b),
    inference(rename_variable,[status(thm)],[s10]) ).

fof(s29,plain,
    ? [X29] :
    ! [X5,X7] :
    ? [X6] :
    ! [X8] : r(X7,X29),
    inference(rename_variable,[status(thm)],[s7]) ).

fof(s30,plain,
    ! [X5,X7,X8] : r(X7,b),
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s31,plain,
    ! [X17,X7,X8] : r(X7,b),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X6,sK1(X7,X17))],[s14]) ).

fof(s32,plain,
    ~ ~ ! [X4] : p(b),
    inference(double_negation,[status(thm)],[s18]) ).

fof(s33,plain,
    ? [X30] :
    ! [X17,X7,X8] : r(X7,X30),
    inference(existential_gen,[status(thm)],[s31]) ).

fof(s34,plain,
    ( ! [X31] :
      ? [X32] : p(X31)
   => ? [X24] :
        ( ( ( q(g(a,b))
            | r(a,g(X24,a)) )
        <=> ! [X14] :
            ? [X15] : q(g(a,a)) )
       => ! [X0,X2] :
          ? [X1] :
            ( t
            & r(X1,X1) ) ) ),
    inference(add_hypothesis,[status(thm)],[s26]) ).

fof(s35,plain,
    ? [X33] :
      ( ( ( q(g(a,b))
          | r(a,g(X33,a)) )
      <=> ! [X14] :
          ? [X15] : q(g(a,a)) )
     => ! [X0,X2] :
        ? [X1] :
          ( t
          & r(X1,X1) ) ),
    inference(rename_variable,[status(thm)],[s26]) ).

fof(s36,plain,
    ( ? [X21] :
      ! [X5,X7,X8] : r(X7,X21)
    & ! [X4] : p(b) ),
    inference(conjunction,[status(thm)],[s17,s18]) ).

fof(s37,plain,
    ! [X9] :
    ? [X10] : t,
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s38,plain,
    ? [X34] :
      ( ( ( q(g(a,b))
          | r(a,g(X34,a)) )
      <=> ! [X14] :
          ? [X15] : q(g(a,a)) )
     => ! [X0,X2] :
        ? [X1] :
          ( t
          & r(X1,X1) ) ),
    inference(rename_variable,[status(thm)],[s26]) ).

fof(s39,plain,
    ? [X10] : t,
    inference(instantiate,[status(thm)],[s12]) ).

fof(s40,plain,
    ( ~ ( c = b
       => t )
   => ( ~ ! [X16] :
            ( r(a,a)
            & f(a) = X16 )
      | ! [X16] :
          ( r(a,a)
          & f(a) = X16 ) ) ),
    inference(add_hypothesis,[status(thm)],[s13]) ).

fof(s41,plain,
    ! [X8] : r(b,b),
    inference(instantiate,[status(thm)],[s15]) ).

fof(s42,plain,
    ! [X17,X7,X8] : r(X7,b),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X6,sK2(X17,X7))],[s14]) ).

fof(s43,plain,
    ? [X21] :
    ! [X5,X7,X8] : r(X7,X21),
    inference(split_conjunct,[status(thm)],[s36]) ).

fof(s44,plain,
    ( ( q(g(f(a),g(b,b)))
    <=> ( p(f(a))
        | t ) )
    | ~ ( q(g(f(a),g(b,b)))
      <=> ( p(f(a))
          | t ) ) ),
    inference(excluded_middle,[status(thm)],[s11]) ).

fof(s45,plain,
    ( ( ! [X18] :
        ? [X19] : b = f(a)
      & ? [X20] : r(a,g(a,X20)) )
    | ! [X11] :
      ? [X12] : r(f(g(X11,a)),f(f(c))) ),
    inference(commute,[status(thm)],[s16]) ).

fof(s46,plain,
    ! [X35] : r(b,b),
    inference(rename_variable,[status(thm)],[s41]) ).

fof(s47,plain,
    ( ( ( q(g(a,b))
        | r(a,g(sK3,a)) )
    <=> ! [X14] :
        ? [X15] : q(g(a,a)) )
   => ! [X0,X2] :
      ? [X1] :
        ( t
        & r(X1,X1) ) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X24,sK3)],[s26]) ).

fof(s48,plain,
    ! [X5,X7,X8] : r(X7,b),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK4]),skolemize(X6,sK4(X5,X7))],[s2]) ).

fof(s49,plain,
    ? [X36] :
    ! [X8] : r(X36,X36),
    inference(existential_gen,[status(thm)],[s41]) ).

fof(s50,plain,
    ( ! [X37] :
      ? [X38] : ~ q(c)
    | ~ ! [X37] :
        ? [X38] : ~ q(c) ),
    inference(excluded_middle,[status(thm)],[s39]) ).

fof(s51,plain,
    ( q(c)
    | ~ q(c) ),
    inference(excluded_middle,[status(thm)],[s29]) ).

fof(s52,plain,
    ( ! [X4] : p(b)
    & ? [X21] :
      ! [X5,X7,X8] : r(X7,X21) ),
    inference(commute,[status(thm)],[s36]) ).

fof(s53,plain,
    ( q(c)
   => ( ! [X37] :
        ? [X38] : ~ q(c)
      | ~ ! [X37] :
          ? [X38] : ~ q(c) ) ),
    inference(add_hypothesis,[status(thm)],[s50]) ).

fof(s54,plain,
    ( ? [X36] :
      ! [X8] : r(X36,X36)
    | ! [X39] :
      ? [X40,X41] : q(X39) ),
    inference(weaken,[status(thm)],[s49]) ).

fof(negc,negated_conjecture,
    ~ ( ? [X36] :
        ! [X8] : r(X36,X36)
      | ! [X39] :
        ? [X40,X41] : q(X39) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s54]) ).

% SZS output end Proof
