%------------------------------------------------------------------------------
% File     : PRV011+1.s : ProoVer 2026
% Proof    : Problems/PRV011+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] :
    ! [X3] :
    ? [X4] :
      ( q(f(c))
     => a = a ),
    file('Problems/PRV011+1.p',s0) ).

fof(s1,axiom,
    ! [X5] :
      ( ! [X6] : t
    <=> ( r(c,X5)
       => q(X5) ) ),
    file('Problems/PRV011+1.p',s1) ).

fof(s2,axiom,
    ! [X7,X9] :
    ? [X8] : p(a),
    file('Problems/PRV011+1.p',s2) ).

fof(s3,axiom,
    ! [X10] :
      ( ~ p(a)
     => ~ r(X10,X10) ),
    file('Problems/PRV011+1.p',s3) ).

fof(s4,axiom,
    p(f(f(a))),
    file('Problems/PRV011+1.p',s4) ).

fof(c,conjecture,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
        ( q(f(c))
       => a = a )
    | ! [X26] :
      ? [X27] :
        ( t
        & t ) ),
    file('Problems/PRV011+1.p',c) ).

fof(s5,plain,
    ! [X9] :
    ? [X8] : p(a),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s2]) ).

fof(s6,plain,
    ! [X7,X9] : p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X8,sK0(X7,X9))],[s2]) ).

fof(s7,plain,
    c = c,
    inference(reflexivity,[status(thm)],[s2]) ).

fof(s8,plain,
    ? [X8] : p(a),
    inference(instantiate,[status(thm)],[s5]) ).

fof(s9,plain,
    ( ! [X10] :
        ( ~ p(a)
       => ~ r(X10,X10) )
    | ! [X11] : f(X11) = a ),
    inference(weaken,[status(thm)],[s3]) ).

fof(s10,plain,
    ! [X9] :
    ? [X8] : p(a),
    inference(instantiate,[status(thm)],[s2]) ).

fof(s11,plain,
    ? [X12] :
    ! [X10] :
      ( ~ p(X12)
     => ~ r(X10,X10) ),
    inference(existential_gen,[status(thm)],[s3]) ).

fof(s12,plain,
    ( ? [X12] :
      ! [X10] :
        ( ~ p(X12)
       => ~ r(X10,X10) )
    & c = c ),
    inference(conjunction,[status(thm)],[s11,s7]) ).

fof(s13,plain,
    ? [X12] :
    ! [X10] :
      ( ~ p(X12)
     => ~ r(X10,X10) ),
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s14,plain,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
        ( q(f(c))
       => a = a )
    | ( t
     => ! [X13] :
        ? [X14] : t ) ),
    inference(weaken,[status(thm)],[s0]) ).

fof(s15,plain,
    ( ( ! [X0,X2] :
        ? [X1] :
        ! [X3] :
        ? [X4] :
          ( q(f(c))
         => a = a )
      | ( t
       => ! [X13] :
          ? [X14] : t ) )
    & c = c ),
    inference(conjunction,[status(thm)],[s14,s7]) ).

fof(s16,plain,
    ( ! [X15] :
      ? [X16] :
      ! [X17] :
      ? [X18] : p(a)
    | ~ ! [X15] :
        ? [X16] :
        ! [X17] :
        ? [X18] : p(a) ),
    inference(excluded_middle,[status(thm)],[s3]) ).

fof(s17,plain,
    ? [X19] : X19 = X19,
    inference(existential_gen,[status(thm)],[s7]) ).

fof(s18,plain,
    ? [X8] : p(a),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m1])],[s5]) ).

fof(s19,plain,
    ? [X20] : p(a),
    inference(rename_variable,[status(thm)],[s8]) ).

fof(s20,plain,
    ! [X0,X2,X3] :
    ? [X4] :
      ( q(f(c))
     => a = a ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X1,sK1(X0,X2))],[s0]) ).

fof(s21,plain,
    ~ ~ ! [X7,X9] :
        ? [X8] : p(a),
    inference(double_negation,[status(thm)],[s2]) ).

fof(s22,plain,
    ~ ~ ? [X8] : p(a),
    inference(double_negation,[status(thm)],[s8]) ).

fof(s23,plain,
    ! [X2,X3] :
    ? [X4] :
      ( q(f(c))
     => a = a ),
    inference(instantiate,[status(thm)],[s20]) ).

fof(s24,plain,
    ! [X10] :
      ( ~ p(sK2)
     => ~ r(X10,X10) ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X12,sK2)],[s11]) ).

fof(s25,plain,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
        ( q(f(c))
       => a = a )
    | ( t
     => ! [X13] :
        ? [X14] : t ) ),
    inference(split_conjunct,[status(thm)],[s15]) ).

fof(s26,plain,
    p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK3]),skolemize(X20,sK3)],[s19]) ).

fof(s27,plain,
    ~ ~ ! [X5] :
          ( ! [X6] : t
        <=> ( r(c,X5)
           => q(X5) ) ),
    inference(double_negation,[status(thm)],[s1]) ).

fof(s28,plain,
    ( p(b)
    | ~ p(b) ),
    inference(excluded_middle,[status(thm)],[s23]) ).

fof(s29,plain,
    ( ~ p(sK2)
   => ~ r(b,b) ),
    inference(instantiate,[status(thm)],[s24]) ).

fof(s30,plain,
    a = a,
    inference(reflexivity,[status(thm)],[s26]) ).

fof(s31,plain,
    ! [X0,X2,X3] :
    ? [X4] :
      ( q(f(c))
     => a = a ),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK4]),skolemize(X1,sK4(X2,X0))],[s0]) ).

fof(s32,plain,
    ( ? [X20] : p(a)
    & ? [X19] : X19 = X19 ),
    inference(conjunction,[status(thm)],[s19,s17]) ).

fof(s33,plain,
    ( c = c
    & ( ! [X0,X2] :
        ? [X1] :
        ! [X3] :
        ? [X4] :
          ( q(f(c))
         => a = a )
      | ( t
       => ! [X13] :
          ? [X14] : t ) ) ),
    inference(commute,[status(thm)],[s15]) ).

fof(s34,plain,
    ! [X9] :
    ? [X8] : p(a),
    inference(instantiate,[status(thm),new_symbols(herbrand,[m2])],[s2]) ).

fof(s35,plain,
    ? [X21] :
    ! [X10] :
      ( ~ p(X21)
     => ~ r(X10,X10) ),
    inference(rename_variable,[status(thm)],[s11]) ).

fof(s36,plain,
    ! [X7,X9] : p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK5]),skolemize(X8,sK5(X7,X9))],[s2]) ).

fof(s37,plain,
    p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK6]),skolemize(X20,sK6)],[s19]) ).

fof(s38,plain,
    ( ! [X22,X23] : q(f(b))
   => ~ ~ ? [X8] : p(a) ),
    inference(add_hypothesis,[status(thm)],[s22]) ).

fof(s39,plain,
    ! [X9] : p(a),
    inference(instantiate,[status(thm)],[s6]) ).

fof(s40,plain,
    ? [X24] :
    ! [X9] :
    ? [X8] : p(X24),
    inference(existential_gen,[status(thm)],[s34]) ).

fof(s41,plain,
    ( ~ ( q(f(c))
      <=> t )
    | ~ ~ ( q(f(c))
        <=> t ) ),
    inference(excluded_middle,[status(thm)],[s35]) ).

fof(s42,plain,
    ! [X7,X9] :
    ? [X8] : p(a),
    inference(remove_double_negation,[status(thm)],[s21]) ).

fof(s43,plain,
    ( c = c
    & ! [X7,X9] :
      ? [X8] : p(a) ),
    inference(conjunction,[status(thm)],[s7,s2]) ).

fof(s44,plain,
    ? [X25] :
      ( p(X25)
      | ~ p(X25) ),
    inference(existential_gen,[status(thm)],[s28]) ).

fof(s45,plain,
    c = c,
    inference(split_conjunct,[status(thm)],[s12]) ).

fof(s46,plain,
    ? [X8] : p(a),
    inference(remove_double_negation,[status(thm)],[s22]) ).

fof(s47,plain,
    b = b,
    inference(reflexivity,[status(thm)],[s32]) ).

fof(s48,plain,
    ! [X7,X9] : p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK7]),skolemize(X8,sK7(X9,X7))],[s2]) ).

fof(s49,plain,
    p(a),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK8]),skolemize(X8,sK8)],[s46]) ).

fof(s50,plain,
    ( ! [X0,X2] :
      ? [X1] :
      ! [X3] :
      ? [X4] :
        ( q(f(c))
       => a = a )
    | ! [X26] :
      ? [X27] :
        ( t
        & t ) ),
    inference(weaken,[status(thm)],[s0]) ).

fof(negc,negated_conjecture,
    ~ ( ! [X0,X2] :
        ? [X1] :
        ! [X3] :
        ? [X4] :
          ( q(f(c))
         => a = a )
      | ! [X26] :
        ? [X27] :
          ( t
          & t ) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s50]) ).

% SZS output end Proof
