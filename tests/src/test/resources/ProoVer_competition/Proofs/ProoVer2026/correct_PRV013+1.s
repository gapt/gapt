%------------------------------------------------------------------------------
% File     : PRV013+1.s : ProoVer 2026
% Proof    : Problems/PRV013+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    file('Problems/PRV013+1.p',s0) ).

fof(s1,axiom,
    ! [X4,X5] :
    ? [X6] :
      ( t
      & p(X4) ),
    file('Problems/PRV013+1.p',s1) ).

fof(s2,axiom,
    ! [X7,X9] :
    ? [X8] :
    ! [X10] :
    ? [X11,X12] : t,
    file('Problems/PRV013+1.p',s2) ).

fof(s3,axiom,
    ( ? [X13] : p(f(X13))
   => ! [X14,X15] :
      ? [X16] : t ),
    file('Problems/PRV013+1.p',s3) ).

fof(s4,axiom,
    ! [X17] :
    ? [X18] : q(g(a,b)),
    file('Problems/PRV013+1.p',s4) ).

fof(c,conjecture,
    ( ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t )
    | ! [X19] :
      ? [X20] : t
    | ~ ~ q(a) ),
    file('Problems/PRV013+1.p',c) ).

fof(s5,plain,
    ! [X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(m0) = g(b,X2) ),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s0]) ).

fof(s6,plain,
    ( ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t )
    & ! [X0,X2] :
      ? [X1,X3] :
        ( f(c) = X2
        & f(X0) = g(b,X2) ) ),
    inference(conjunction,[status(thm)],[s3,s0]) ).

fof(s7,plain,
    ( ? [X13] : p(f(X13))
   => ! [X14,X15] :
      ? [X16] : t ),
    inference(split_conjunct,[status(thm)],[s6]) ).

fof(s8,plain,
    ! [X0,X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(split_conjunct,[status(thm)],[s6]) ).

fof(s9,plain,
    ( ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t )
    | ! [X19] :
      ? [X20] : t ),
    inference(weaken,[status(thm)],[s3]) ).

fof(s10,plain,
    ? [X21] :
    ! [X0,X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(X0) = g(X21,X2) ),
    inference(existential_gen,[status(thm)],[s0]) ).

fof(s11,plain,
    ( ! [X19] :
      ? [X20] : t
    | ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t ) ),
    inference(commute,[status(thm)],[s9]) ).

fof(s12,plain,
    ! [X0,X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(split_conjunct,[status(thm)],[s6]) ).

fof(s13,plain,
    ! [X2] :
    ? [X3] :
      ( f(c) = X2
      & f(m0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X1,sK0(X2))],[s5]) ).

fof(s14,plain,
    a = a,
    inference(reflexivity,[status(thm)],[s9]) ).

fof(s15,plain,
    ! [X0,X2] :
    ? [X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X1,sK1(X0,X2))],[s12]) ).

fof(s16,plain,
    ! [X0,X2] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X3,sK2(X0,X2))],[s15]) ).

fof(s17,plain,
    ( ! [X17] :
      ? [X18] : q(g(a,b))
    & ( ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t )
      | ! [X19] :
        ? [X20] : t ) ),
    inference(conjunction,[status(thm)],[s4,s9]) ).

fof(s18,plain,
    ( ( ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t )
      | ! [X19] :
        ? [X20] : t )
    & ! [X17] :
      ? [X18] : q(g(a,b)) ),
    inference(commute,[status(thm)],[s17]) ).

fof(s19,plain,
    ! [X22] :
    ? [X18] : q(g(a,b)),
    inference(rename_variable,[status(thm)],[s4]) ).

fof(s20,plain,
    ( ( ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t )
      | ! [X19] :
        ? [X20] : t )
    & ! [X17] :
      ? [X18] : q(g(a,b)) ),
    inference(commute,[status(thm)],[s17]) ).

fof(s21,plain,
    ( ? [X13] : p(f(X13))
   => ! [X14,X15] :
      ? [X16] : t ),
    inference(split_conjunct,[status(thm)],[s6]) ).

fof(s22,plain,
    ( ! [X0,X2] :
      ? [X1,X3] :
        ( f(c) = X2
        & f(X0) = g(b,X2) )
    & ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t ) ),
    inference(commute,[status(thm)],[s6]) ).

fof(s23,plain,
    ? [X23] :
    ! [X2] :
    ? [X1,X3] :
      ( f(X23) = X2
      & f(m0) = g(b,X2) ),
    inference(existential_gen,[status(thm)],[s5]) ).

fof(s24,plain,
    ( ? [X13] : p(f(X13))
   => ! [X14,X15] :
      ? [X16] : t ),
    inference(split_conjunct,[status(thm)],[s6]) ).

fof(s25,plain,
    ? [X24] :
      ( ! [X0,X2] :
        ? [X1,X3] :
          ( f(c) = X2
          & f(X0) = g(X24,X2) )
      & ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t ) ),
    inference(existential_gen,[status(thm)],[s22]) ).

fof(s26,plain,
    ! [X0,X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(split_conjunct,[status(thm)],[s22]) ).

fof(s27,plain,
    ( ! [X17] :
      ? [X18] : q(g(a,b))
    & ( ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t )
      | ! [X19] :
        ? [X20] : t ) ),
    inference(commute,[status(thm)],[s20]) ).

fof(s28,plain,
    ( ? [X23] :
      ! [X2] :
      ? [X1,X3] :
        ( f(X23) = X2
        & f(m0) = g(b,X2) )
    | ! [X25,X26] :
      ? [X27] : t ),
    inference(weaken,[status(thm)],[s23]) ).

fof(s29,plain,
    ? [X28] :
    ! [X22] :
    ? [X18] : q(X28),
    inference(existential_gen,[status(thm)],[s19]) ).

fof(s30,plain,
    ! [X17] :
    ? [X18] : q(g(a,b)),
    inference(split_conjunct,[status(thm)],[s27]) ).

fof(s31,plain,
    ? [X18] : q(g(a,b)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m1])],[s19]) ).

fof(s32,plain,
    ! [X29] :
    ? [X18] : q(g(a,b)),
    inference(rename_variable,[status(thm)],[s4]) ).

fof(s33,plain,
    ! [X7,X9,X10] :
    ? [X11,X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X8,sK3(X9,X7))],[s2]) ).

fof(s34,plain,
    ( ! [X30,X31] :
      ? [X32] : f(b) = f(b)
    | ~ ! [X30,X31] :
        ? [X32] : f(b) = f(b) ),
    inference(excluded_middle,[status(thm)],[s18]) ).

fof(s35,plain,
    ! [X17] : q(g(a,b)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK4]),skolemize(X18,sK4(X17))],[s30]) ).

fof(s36,plain,
    ~ ~ ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t ),
    inference(double_negation,[status(thm)],[s7]) ).

fof(s37,plain,
    ! [X33] :
    ? [X18] : q(g(a,b)),
    inference(rename_variable,[status(thm)],[s32]) ).

fof(s38,plain,
    ( ? [X28] :
      ! [X22] :
      ? [X18] : q(X28)
    | ( ~ q(a)
     => ! [X34] :
        ? [X35] : X34 = c ) ),
    inference(weaken,[status(thm)],[s29]) ).

fof(s39,plain,
    ~ ~ ( ( ( ? [X13] : p(f(X13))
           => ! [X14,X15] :
              ? [X16] : t )
          | ! [X19] :
            ? [X20] : t )
        & ! [X17] :
          ? [X18] : q(g(a,b)) ),
    inference(double_negation,[status(thm)],[s18]) ).

fof(s40,plain,
    ! [X5] :
    ? [X6] :
      ( t
      & p(c) ),
    inference(instantiate,[status(thm)],[s1]) ).

fof(s41,plain,
    ! [X17] :
    ? [X18] : q(g(a,b)),
    inference(split_conjunct,[status(thm)],[s20]) ).

fof(s42,plain,
    ( ! [X25,X26] :
      ? [X27] : t
    | ? [X23] :
      ! [X2] :
      ? [X1,X3] :
        ( f(X23) = X2
        & f(m0) = g(b,X2) ) ),
    inference(commute,[status(thm)],[s28]) ).

fof(s43,plain,
    ? [X6] :
      ( t
      & p(c) ),
    inference(instantiate,[status(thm)],[s40]) ).

fof(s44,plain,
    ! [X2] :
    ? [X1,X3] :
      ( f(c) = X2
      & f(a) = g(b,X2) ),
    inference(instantiate,[status(thm)],[s12]) ).

fof(s45,plain,
    ! [X0,X2] :
    ? [X3] :
      ( f(c) = X2
      & f(X0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK5]),skolemize(X1,sK5(X2,X0))],[s0]) ).

fof(s46,plain,
    ( t
    & p(c) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK6]),skolemize(X6,sK6)],[s43]) ).

fof(s47,plain,
    ! [X2] :
    ? [X3] :
      ( f(c) = X2
      & f(m0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK7]),skolemize(X1,sK7(X2))],[s5]) ).

fof(s48,plain,
    t,
    inference(split_conjunct,[status(thm)],[s46]) ).

fof(s49,plain,
    ! [X5] :
      ( t
      & p(c) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK8]),skolemize(X6,sK8(X5))],[s40]) ).

fof(s50,plain,
    ? [X18] : q(g(a,b)),
    inference(instantiate,[status(thm)],[s19]) ).

fof(s51,plain,
    ( f(g(b,a)) = b
    | f(g(b,a)) != b ),
    inference(excluded_middle,[status(thm)],[s30]) ).

fof(s52,plain,
    ( ! [X0,X2] :
        ( f(c) = X2
        & f(X0) = g(b,X2) )
    & ! [X0,X2] :
      ? [X3] :
        ( f(c) = X2
        & f(X0) = g(b,X2) ) ),
    inference(conjunction,[status(thm)],[s16,s15]) ).

fof(s53,plain,
    ! [X17] :
    ? [X18] : q(g(a,b)),
    inference(split_conjunct,[status(thm)],[s27]) ).

fof(s54,plain,
    ! [X2] :
    ? [X3] :
      ( f(c) = X2
      & f(m0) = g(b,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK9]),skolemize(X1,sK9(X2))],[s5]) ).

fof(s55,plain,
    ( ( ? [X13] : p(f(X13))
     => ! [X14,X15] :
        ? [X16] : t )
    | ! [X19] :
      ? [X20] : t
    | ~ ~ q(a) ),
    inference(weaken,[status(thm)],[s9]) ).

fof(negc,negated_conjecture,
    ~ ( ( ? [X13] : p(f(X13))
       => ! [X14,X15] :
          ? [X16] : t )
      | ! [X19] :
        ? [X20] : t
      | ~ ~ q(a) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s55]) ).

% SZS output end Proof
