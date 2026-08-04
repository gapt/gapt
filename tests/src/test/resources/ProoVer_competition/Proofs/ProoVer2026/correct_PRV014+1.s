%------------------------------------------------------------------------------
% File     : PRV014+1.s : ProoVer 2026
% Proof    : Problems/PRV014+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    file('Problems/PRV014+1.p',s0) ).

fof(s1,axiom,
    ! [X6,X7] : ~ p(b),
    file('Problems/PRV014+1.p',s1) ).

fof(s2,axiom,
    ! [X8,X10] :
    ? [X9] :
      ~ ~ p(f(b)),
    file('Problems/PRV014+1.p',s2) ).

fof(s3,axiom,
    ~ ( q(c)
      & f(b) != c ),
    file('Problems/PRV014+1.p',s3) ).

fof(c,conjecture,
    ( ~ ~ ~ ( q(c)
            & f(b) != c )
    | ! [X32,X33] :
      ? [X34] : t ),
    file('Problems/PRV014+1.p',c) ).

fof(s4,plain,
    ! [X10] :
    ? [X9] :
      ~ ~ p(f(b)),
    inference(instantiate,[status(thm)],[s2]) ).

fof(s5,plain,
    ! [X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(instantiate,[status(thm)],[s0]) ).

fof(s6,plain,
    ! [X8,X10] :
      ~ ~ p(f(b)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X9,sK0(X8,X10))],[s2]) ).

fof(s7,plain,
    ! [X11] :
    ? [X9] :
      ~ ~ p(f(b)),
    inference(rename_variable,[status(thm)],[s4]) ).

fof(s8,plain,
    ( ~ ( q(c)
        & f(b) != c )
    | ~ ! [X12] :
        ? [X13] : q(X12) ),
    inference(weaken,[status(thm)],[s3]) ).

fof(s9,plain,
    ! [X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(instantiate,[status(thm)],[s0]) ).

fof(s10,plain,
    ~ ~ ! [X8,X10] :
        ? [X9] :
          ~ ~ p(f(b)),
    inference(double_negation,[status(thm)],[s2]) ).

fof(s11,plain,
    ~ ~ ! [X8,X10] :
        ? [X9] :
          ~ ~ p(f(b)),
    inference(double_negation,[status(thm)],[s2]) ).

fof(s12,plain,
    ( ~ ( q(c)
        & f(b) != c )
    & ! [X10] :
      ? [X9] :
        ~ ~ p(f(b)) ),
    inference(conjunction,[status(thm)],[s3,s4]) ).

fof(s13,plain,
    ~ ( q(c)
      & f(b) != c ),
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s14,plain,
    ( ~ q(c)
    | ~ ( f(b) != c ) ),
    inference(de_morgan,[status(thm)],[s3]) ).

fof(s15,plain,
    ? [X9] :
      ~ ~ p(f(b)),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s4]) ).

fof(s16,plain,
    ( ~ ( f(b) != c )
    | ~ q(c) ),
    inference(commute,[status(thm)],[s14]) ).

fof(s17,plain,
    ( ! [X10] :
      ? [X9] :
        ~ ~ p(f(b))
    & ~ ( q(c)
        & f(b) != c ) ),
    inference(commute,[status(thm)],[s12]) ).

fof(s18,plain,
    ( ! [X10] :
      ? [X9] :
        ~ ~ p(f(b))
    & ~ ( q(c)
        & f(b) != c )
    & ! [X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
      ! [X5] : r(f(c),X3) ),
    inference(conjunction,[status(thm)],[s17,s9]) ).

fof(s19,plain,
    ( ? [X14] : r(g(X14,b),X14)
    | ! [X15] :
      ? [X16] : q(f(c))
    | ~ ( ? [X14] : r(g(X14,b),X14)
        | ! [X15] :
          ? [X16] : q(f(c)) ) ),
    inference(excluded_middle,[status(thm)],[s6]) ).

fof(s20,plain,
    ! [X2,X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X1,sK1(X2))],[s5]) ).

fof(s21,plain,
    ! [X17,X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(rename_variable,[status(thm)],[s0]) ).

fof(s22,plain,
    ! [X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(instantiate,[status(thm)],[s21]) ).

fof(s23,plain,
    ~ ~ ~ ( q(c)
          & f(b) != c ),
    inference(double_negation,[status(thm)],[s13]) ).

fof(s24,plain,
    ( ~ r(a,f(f(c)))
   => ~ ( q(c)
        & f(b) != c ) ),
    inference(add_hypothesis,[status(thm)],[s3]) ).

fof(s25,plain,
    ? [X18] :
      ( ~ r(a,f(f(X18)))
     => ~ ( q(X18)
          & f(b) != X18 ) ),
    inference(existential_gen,[status(thm)],[s24]) ).

fof(s26,plain,
    ( ! [X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
      ! [X5] : r(f(c),X3)
    | ( p(b)
     => t ) ),
    inference(weaken,[status(thm)],[s9]) ).

fof(s27,plain,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
      ! [X5] : r(f(c),X3)
    & ! [X10] :
      ? [X9] :
        ~ ~ p(f(b))
    & ~ ( q(c)
        & f(b) != c )
    & ! [X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
      ! [X5] : r(f(c),X3) ),
    inference(conjunction,[status(thm)],[s0,s18]) ).

fof(s28,plain,
    c = c,
    inference(reflexivity,[status(thm)],[s19]) ).

fof(s29,plain,
    ! [X8,X10] :
      ~ ~ p(f(b)),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X9,sK2(X8,X10))],[s2]) ).

fof(s30,plain,
    ~ ~ ! [X8,X10] :
          ~ ~ p(f(b)),
    inference(double_negation,[status(thm)],[s29]) ).

fof(s31,plain,
    ( ! [X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
      ! [X5] : r(f(c),X3)
    | ( p(b)
     => t )
    | ~ ! [X19] :
        ? [X20] : r(f(c),a) ),
    inference(weaken,[status(thm)],[s26]) ).

fof(s32,plain,
    c = c,
    inference(reflexivity,[status(thm)],[s14]) ).

fof(s33,plain,
    ~ ~ ~ ( q(c)
          & f(b) != c ),
    inference(double_negation,[status(thm)],[s13]) ).

fof(s34,plain,
    ! [X10] :
    ? [X9] :
      ~ ~ p(f(b)),
    inference(split_conjunct,[status(thm)],[s17]) ).

fof(s35,plain,
    ( ? [X21] :
      ! [X22] :
      ? [X23] : t
    | ~ ? [X21] :
        ! [X22] :
        ? [X23] : t ),
    inference(excluded_middle,[status(thm)],[s15]) ).

fof(s36,plain,
    ( ( ! [X24] :
        ? [X25] : t
      | ? [X26] : r(X26,g(X26,X26)) )
   => ( ! [X2] :
        ? [X1] :
        ! [X3] :
        ? [X4] :
        ! [X5] : r(f(c),X3)
      | ( p(b)
       => t )
      | ~ ! [X19] :
          ? [X20] : r(f(c),a) ) ),
    inference(add_hypothesis,[status(thm)],[s31]) ).

fof(s37,plain,
    ! [X10] :
      ~ ~ p(f(b)),
    inference(instantiate,[status(thm)],[s6]) ).

fof(s38,plain,
    ! [X27,X10] :
    ? [X9] :
      ~ ~ p(f(b)),
    inference(rename_variable,[status(thm)],[s2]) ).

fof(s39,plain,
    ! [X28,X10] :
      ~ ~ p(f(b)),
    inference(rename_variable,[status(thm)],[s6]) ).

fof(s40,plain,
    ? [X29] :
      ( ~ ( X29 != c )
      | ~ q(c) ),
    inference(existential_gen,[status(thm)],[s16]) ).

fof(s41,plain,
    ? [X30] :
      ( ~ q(X30)
      | ~ ( f(b) != X30 ) ),
    inference(existential_gen,[status(thm)],[s14]) ).

fof(s42,plain,
    ! [X2,X3] :
    ? [X4] :
    ! [X5] : r(f(c),X3),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X1,sK3(X2))],[s9]) ).

fof(s43,plain,
    ~ ( q(c)
      & f(b) != c ),
    inference(remove_double_negation,[status(thm)],[s23]) ).

fof(s44,plain,
    ? [X31,X9] :
      ~ ~ p(X31),
    inference(existential_gen,[status(thm)],[s15]) ).

fof(s45,plain,
    ~ ~ ! [X2] :
        ? [X1] :
        ! [X3] :
        ? [X4] :
        ! [X5] : r(f(c),X3),
    inference(double_negation,[status(thm)],[s9]) ).

fof(s46,plain,
    ( ~ ~ ~ ( q(c)
            & f(b) != c )
    | ! [X32,X33] :
      ? [X34] : t ),
    inference(weaken,[status(thm)],[s33]) ).

fof(negc,negated_conjecture,
    ~ ( ~ ~ ~ ( q(c)
              & f(b) != c )
      | ! [X32,X33] :
        ? [X34] : t ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s46]) ).

% SZS output end Proof
