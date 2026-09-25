%------------------------------------------------------------------------------
% File     : PRV015+1.s : ProoVer 2026
% Proof    : Problems/PRV015+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] :
      ~ ( X2 != X1 ),
    file('Problems/PRV015+1.p',s0) ).

fof(s1,axiom,
    ! [X3] :
      ( ? [X4] : r(g(X4,b),g(X4,c))
     => ! [X5] :
        ? [X6] : b = a ),
    file('Problems/PRV015+1.p',s1) ).

fof(s2,axiom,
    ! [X7,X9] :
    ? [X8] :
    ! [X10] :
    ? [X11,X12] : t,
    file('Problems/PRV015+1.p',s2) ).

fof(s3,axiom,
    p(a),
    file('Problems/PRV015+1.p',s3) ).

fof(s4,axiom,
    ( ! [X13] : p(f(f(X13)))
    | t ),
    file('Problems/PRV015+1.p',s4) ).

fof(c,conjecture,
    ( ( ! [X31] :
        ? [X32] : t
     => ( t
        & p(g(b,b)) ) )
    | ~ ( ! [X31] :
          ? [X32] : t
       => ( t
          & p(g(b,b)) ) )
    | q(c) ),
    file('Problems/PRV015+1.p',c) ).

fof(s5,plain,
    ( p(a)
    & ! [X3] :
        ( ? [X4] : r(g(X4,b),g(X4,c))
       => ! [X5] :
          ? [X6] : b = a ) ),
    inference(conjunction,[status(thm)],[s3,s1]) ).

fof(s6,plain,
    ! [X0,X2] :
      ~ ( X2 != sK0(X2,X0) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X1,sK0(X2,X0))],[s0]) ).

fof(s7,plain,
    ( t
    | ~ t ),
    inference(excluded_middle,[status(thm)],[s2]) ).

fof(s8,plain,
    ( ! [X0,X2] :
      ? [X1] :
        ~ ( X2 != X1 )
    | ! [X14] : r(X14,X14)
    | ! [X15] :
      ? [X16] : r(X15,b) ),
    inference(weaken,[status(thm)],[s0]) ).

fof(s9,plain,
    ( ! [X13] : p(f(f(X13)))
    | t
    | ( ! [X17] : p(X17)
      & t
      & g(a,b) = f(a) ) ),
    inference(weaken,[status(thm)],[s4]) ).

fof(s10,plain,
    b = b,
    inference(reflexivity,[status(thm)],[s2]) ).

fof(s11,plain,
    ! [X7,X9,X10] :
    ? [X11,X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X8,sK1(X7,X9))],[s2]) ).

fof(s12,plain,
    ~ ~ ! [X7,X9,X10] :
        ? [X11,X12] : t,
    inference(double_negation,[status(thm)],[s11]) ).

fof(s13,plain,
    ! [X18,X2] :
    ? [X1] :
      ~ ( X2 != X1 ),
    inference(rename_variable,[status(thm)],[s0]) ).

fof(s14,plain,
    ? [X19] :
    ! [X3] :
      ( ? [X4] : r(g(X4,b),g(X4,c))
     => ! [X5] :
        ? [X6] : b = X19 ),
    inference(existential_gen,[status(thm)],[s1]) ).

fof(s15,plain,
    ( ! [X20] :
      ? [X21] : q(b)
    | ~ ! [X20] :
        ? [X21] : q(b) ),
    inference(excluded_middle,[status(thm)],[s11]) ).

fof(s16,plain,
    ( ! [X7,X9] :
      ? [X8] :
      ! [X10] :
      ? [X11,X12] : t
    & p(a) ),
    inference(conjunction,[status(thm)],[s2,s3]) ).

fof(s17,plain,
    ( ? [X22] :
      ! [X23] :
      ? [X24] : q(X22)
   => ( ! [X0,X2] :
        ? [X1] :
          ~ ( X2 != X1 )
      | ! [X14] : r(X14,X14)
      | ! [X15] :
        ? [X16] : r(X15,b) ) ),
    inference(add_hypothesis,[status(thm)],[s8]) ).

fof(s18,plain,
    p(a),
    inference(split_conjunct,[status(thm)],[s5]) ).

fof(s19,plain,
    ! [X25,X9] :
    ? [X8] :
    ! [X10] :
    ? [X11,X12] : t,
    inference(rename_variable,[status(thm)],[s2]) ).

fof(s20,plain,
    ! [X7,X9,X10] :
    ? [X11,X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X8,sK2(X7,X9))],[s2]) ).

fof(s21,plain,
    ! [X25,X9,X10] :
    ? [X11,X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X8,sK3(X9,X25))],[s19]) ).

fof(s22,plain,
    ? [X26] : p(X26),
    inference(existential_gen,[status(thm)],[s18]) ).

fof(s23,plain,
    ! [X7,X9,X10] :
    ? [X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK4]),skolemize(X11,sK4(X9,X7,X10))],[s20]) ).

fof(s24,plain,
    ! [X27,X2] :
    ? [X1] :
      ~ ( X2 != X1 ),
    inference(rename_variable,[status(thm)],[s13]) ).

fof(s25,plain,
    ( ! [X7,X9,X10] :
      ? [X12] : t
    & ! [X7,X9,X10] :
      ? [X11,X12] : t ),
    inference(conjunction,[status(thm)],[s23,s20]) ).

fof(s26,plain,
    ( ! [X28] : ~ r(X28,b)
    | ~ ! [X28] : ~ r(X28,b) ),
    inference(excluded_middle,[status(thm)],[s15]) ).

fof(s27,plain,
    ! [X29,X9,X10] :
    ? [X11,X12] : t,
    inference(rename_variable,[status(thm)],[s20]) ).

fof(s28,plain,
    ! [X30,X2] :
    ? [X1] :
      ~ ( X2 != X1 ),
    inference(rename_variable,[status(thm)],[s24]) ).

fof(s29,plain,
    ( ( ! [X31] :
        ? [X32] : t
     => ( t
        & p(g(b,b)) ) )
    | ~ ( ! [X31] :
          ? [X32] : t
       => ( t
          & p(g(b,b)) ) ) ),
    inference(excluded_middle,[status(thm)],[s24]) ).

fof(s30,plain,
    ? [X33] : X33 = X33,
    inference(existential_gen,[status(thm)],[s10]) ).

fof(s31,plain,
    ? [X34,X19] :
    ! [X3] :
      ( ? [X4] : r(g(X4,b),g(X4,X34))
     => ! [X5] :
        ? [X6] : b = X19 ),
    inference(existential_gen,[status(thm)],[s14]) ).

fof(s32,plain,
    ? [X35] : p(X35),
    inference(existential_gen,[status(thm)],[s18]) ).

fof(s33,plain,
    ! [X7,X9,X10] :
    ? [X12] : t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK5]),skolemize(X11,sK5(X10,X7,X9))],[s20]) ).

fof(s34,plain,
    ! [X7,X9,X10] :
    ? [X12] : t,
    inference(split_conjunct,[status(thm)],[s25]) ).

fof(s35,plain,
    ! [X7,X9,X10] :
    ? [X11,X12] : t,
    inference(remove_double_negation,[status(thm)],[s12]) ).

fof(s36,plain,
    ? [X36] :
      ( ! [X13] : p(f(f(X13)))
      | t
      | ( ! [X17] : p(X17)
        & t
        & X36 = f(a) ) ),
    inference(existential_gen,[status(thm)],[s9]) ).

fof(s37,plain,
    ! [X27,X2] :
      ~ ( X2 != sK6(X27,X2) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK6]),skolemize(X1,sK6(X27,X2))],[s24]) ).

fof(s38,plain,
    ( ! [X3] :
        ( ? [X4] : r(g(X4,b),g(X4,c))
       => ! [X5] :
          ? [X6] : b = a )
    & p(a) ),
    inference(commute,[status(thm)],[s5]) ).

fof(s39,plain,
    ( ! [X37] :
      ? [X38] :
      ! [X39] :
      ? [X40] : r(X39,X37)
   => ( ! [X7,X9] :
        ? [X8] :
        ! [X10] :
        ? [X11,X12] : t
      & p(a) ) ),
    inference(add_hypothesis,[status(thm)],[s16]) ).

fof(s40,plain,
    ( ( ! [X31] :
        ? [X32] : t
     => ( t
        & p(g(b,b)) ) )
    | ~ ( ! [X31] :
          ? [X32] : t
       => ( t
          & p(g(b,b)) ) )
    | q(c) ),
    inference(weaken,[status(thm)],[s29]) ).

fof(negc,negated_conjecture,
    ~ ( ( ! [X31] :
          ? [X32] : t
       => ( t
          & p(g(b,b)) ) )
      | ~ ( ! [X31] :
            ? [X32] : t
         => ( t
            & p(g(b,b)) ) )
      | q(c) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s40]) ).

% SZS output end Proof
