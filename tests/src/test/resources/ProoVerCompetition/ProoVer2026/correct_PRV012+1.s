%------------------------------------------------------------------------------
% File     : PRV012+1.s : ProoVer 2026
% Proof    : Problems/PRV012+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1,X3] : p(X1),
    file('Problems/PRV012+1.p',s0) ).

fof(s1,axiom,
    ! [X4] :
      ( ? [X5] : r(X4,b)
    <=> ! [X6] :
        ? [X7] : t ),
    file('Problems/PRV012+1.p',s1) ).

fof(s2,axiom,
    ! [X8] :
    ? [X9] : r(X9,f(X9)),
    file('Problems/PRV012+1.p',s2) ).

fof(s3,axiom,
    p(g(a,f(b))),
    file('Problems/PRV012+1.p',s3) ).

fof(s4,axiom,
    ? [X10] :
    ! [X11] :
    ? [X12,X13] : p(g(b,X10)),
    file('Problems/PRV012+1.p',s4) ).

fof(s5,axiom,
    ? [X14] :
      ( ( X14 = b
       => p(b) )
      | ! [X15] : p(X15) ),
    file('Problems/PRV012+1.p',s5) ).

fof(c,conjecture,
    ( ~ ~ ! [X4] :
            ( ? [X5] : r(X4,b)
          <=> ! [X6] :
              ? [X7] : t )
    | ( r(f(g(c,c)),b)
     => ! [X32] :
        ? [X33] : q(X32) ) ),
    file('Problems/PRV012+1.p',c) ).

fof(s6,plain,
    ( ? [X10] :
      ! [X11] :
      ? [X12,X13] : p(g(b,X10))
    | ( t
     => t ) ),
    inference(weaken,[status(thm)],[s4]) ).

fof(s7,plain,
    ? [X9] : r(X9,f(X9)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s2]) ).

fof(s8,plain,
    ~ ~ ! [X4] :
          ( ? [X5] : r(X4,b)
        <=> ! [X6] :
            ? [X7] : t ),
    inference(double_negation,[status(thm)],[s1]) ).

fof(s9,plain,
    ( ! [X4] :
        ( ? [X5] : r(X4,b)
      <=> ! [X6] :
          ? [X7] : t )
    | ! [X16] :
      ? [X17] :
        ( p(X16)
        | X16 = X16 ) ),
    inference(weaken,[status(thm)],[s1]) ).

fof(s10,plain,
    ! [X4] :
      ( ? [X5] : r(X4,b)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(remove_double_negation,[status(thm)],[s8]) ).

fof(s11,plain,
    ( ~ ~ ! [X4] :
            ( ? [X5] : r(X4,b)
          <=> ! [X6] :
              ? [X7] : t )
    & ? [X10] :
      ! [X11] :
      ? [X12,X13] : p(g(b,X10)) ),
    inference(conjunction,[status(thm)],[s8,s4]) ).

fof(s12,plain,
    ( p(g(a,f(b)))
    & ( ? [X10] :
        ! [X11] :
        ? [X12,X13] : p(g(b,X10))
      | ( t
       => t ) ) ),
    inference(conjunction,[status(thm)],[s3,s6]) ).

fof(s13,plain,
    p(g(a,f(b))),
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s14,plain,
    ? [X18] :
    ! [X4] :
      ( ? [X5] : r(X4,X18)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(existential_gen,[status(thm)],[s1]) ).

fof(s15,plain,
    ( ? [X5] : r(m1,b)
  <=> ! [X6] :
      ? [X7] : t ),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m1])],[s10]) ).

fof(s16,plain,
    ! [X4] :
      ( ? [X5] : r(X4,b)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(remove_double_negation,[status(thm)],[s8]) ).

fof(s17,plain,
    ( ! [X19,X20] : p(X20)
    | ~ ! [X19,X20] : p(X20) ),
    inference(excluded_middle,[status(thm)],[s10]) ).

fof(s18,plain,
    ? [X21] :
    ! [X4] :
      ( ? [X5] : r(X4,X21)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(existential_gen,[status(thm)],[s16]) ).

fof(s19,plain,
    ! [X4] :
      ( ? [X5] : r(X4,b)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(remove_double_negation,[status(thm)],[s8]) ).

fof(s20,plain,
    p(g(a,f(b))),
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s21,plain,
    ( ( p(g(a,f(b)))
      & ( ? [X10] :
          ! [X11] :
          ? [X12,X13] : p(g(b,X10))
        | ( t
         => t ) ) )
    | ! [X22] :
      ? [X23] :
      ! [X24] :
      ? [X25] : r(b,g(X24,a)) ),
    inference(weaken,[status(thm)],[s12]) ).

fof(s22,plain,
    ( ! [X4] :
        ( ? [X5] : r(X4,b)
      <=> ! [X6] :
          ? [X7] : t )
    | ~ p(f(b)) ),
    inference(weaken,[status(thm)],[s19]) ).

fof(s23,plain,
    ? [X26] :
    ! [X11] :
    ? [X12,X13] : p(g(b,X26)),
    inference(rename_variable,[status(thm)],[s4]) ).

fof(s24,plain,
    ( ? [X5] : r(m2,b)
  <=> ! [X6] :
      ? [X7] : t ),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m2])],[s10]) ).

fof(s25,plain,
    ~ ~ ! [X4] :
          ( ? [X5] : r(X4,b)
        <=> ! [X6] :
            ? [X7] : t ),
    inference(split_conjunct,[status(thm)],[s11]) ).

fof(s26,plain,
    ( ( ? [X27] : f(a) = f(c)
    <=> r(g(g(b,b),a),a) )
    | ~ ( ? [X27] : f(a) = f(c)
      <=> r(g(g(b,b),a),a) ) ),
    inference(excluded_middle,[status(thm)],[s4]) ).

fof(s27,plain,
    ? [X28,X26] :
    ! [X11] :
    ? [X12,X13] : p(g(X28,X26)),
    inference(existential_gen,[status(thm)],[s23]) ).

fof(s28,plain,
    r(sK0,f(sK0)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X9,sK0)],[s7]) ).

fof(s29,plain,
    ! [X4] :
      ( ? [X5] : r(X4,b)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(remove_double_negation,[status(thm)],[s25]) ).

fof(s30,plain,
    ~ ~ ? [X26] :
        ! [X11] :
        ? [X12,X13] : p(g(b,X26)),
    inference(double_negation,[status(thm)],[s23]) ).

fof(s31,plain,
    ( ? [X10] :
      ! [X11] :
      ? [X12,X13] : p(g(b,X10))
    | ( t
     => t ) ),
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s32,plain,
    ( ? [X10] :
      ! [X11] :
      ? [X12,X13] : p(g(b,X10))
    | ( t
     => t )
    | ( p(b)
    <=> ( q(g(c,c))
      <=> q(f(c)) ) ) ),
    inference(weaken,[status(thm)],[s31]) ).

fof(s33,plain,
    ( ~ ( ? [X27] : f(a) = f(c)
      <=> r(g(g(b,b),a),a) )
    | ( ? [X27] : f(a) = f(c)
    <=> r(g(g(b,b),a),a) ) ),
    inference(commute,[status(thm)],[s26]) ).

fof(s34,plain,
    ! [X11] :
    ? [X12,X13] : p(g(b,sK1)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X10,sK1)],[s4]) ).

fof(s35,plain,
    ( ( ! [X19,X20] : p(X20)
      | ~ ! [X19,X20] : p(X20) )
    & ( ? [X10] :
        ! [X11] :
        ? [X12,X13] : p(g(b,X10))
      | ( t
       => t )
      | ( p(b)
      <=> ( q(g(c,c))
        <=> q(f(c)) ) ) ) ),
    inference(conjunction,[status(thm)],[s17,s32]) ).

fof(s36,plain,
    ? [X29] :
    ! [X4] :
      ( ? [X5] : r(X4,X29)
    <=> ! [X6] :
        ? [X7] : t ),
    inference(rename_variable,[status(thm)],[s18]) ).

fof(s37,plain,
    ! [X11] :
    ? [X13] : p(g(b,sK1)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X12,sK2(X11))],[s34]) ).

fof(s38,plain,
    ( ( sK3 = b
     => p(b) )
    | ! [X15] : p(X15) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X14,sK3)],[s5]) ).

fof(s39,plain,
    ! [X11] : p(g(b,sK1)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK4]),skolemize(X13,sK4(X11))],[s37]) ).

fof(s40,plain,
    ( ! [X30] :
        ( f(a) = X30
        | p(X30) )
    | ~ ! [X30] :
          ( f(a) = X30
          | p(X30) ) ),
    inference(excluded_middle,[status(thm)],[s6]) ).

fof(s41,plain,
    ( ! [X11] :
      ? [X13] : p(g(b,sK1))
    & ( ! [X30] :
          ( f(a) = X30
          | p(X30) )
      | ~ ! [X30] :
            ( f(a) = X30
            | p(X30) ) ) ),
    inference(conjunction,[status(thm)],[s37,s40]) ).

fof(s42,plain,
    ( t
    | ~ t ),
    inference(excluded_middle,[status(thm)],[s0]) ).

fof(s43,plain,
    ( ! [X4] :
        ( ? [X5] : r(X4,b)
      <=> ! [X6] :
          ? [X7] : t )
    | ~ p(f(b))
    | ? [X31] : ~ p(f(X31)) ),
    inference(weaken,[status(thm)],[s22]) ).

fof(s44,plain,
    ( ~ ~ ! [X4] :
            ( ? [X5] : r(X4,b)
          <=> ! [X6] :
              ? [X7] : t )
    | ( r(f(g(c,c)),b)
     => ! [X32] :
        ? [X33] : q(X32) ) ),
    inference(weaken,[status(thm)],[s25]) ).

fof(negc,negated_conjecture,
    ~ ( ~ ~ ! [X4] :
              ( ? [X5] : r(X4,b)
            <=> ! [X6] :
                ? [X7] : t )
      | ( r(f(g(c,c)),b)
       => ! [X32] :
          ? [X33] : q(X32) ) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s44]) ).

% SZS output end Proof
