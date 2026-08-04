%------------------------------------------------------------------------------
% File     : PRV010+1.s : ProoVer 2026
% Proof    : Problems/PRV010+1.p
%------------------------------------------------------------------------------
% SZS output start Proof
fof(s0,axiom,
    ! [X0,X2] :
    ? [X1] : t,
    file('Problems/PRV010+1.p',s0) ).

fof(s1,axiom,
    ! [X3] :
      ( X3 = a
    <=> ( t
        | q(f(X3)) ) ),
    file('Problems/PRV010+1.p',s1) ).

fof(s2,axiom,
    ! [X4] :
    ? [X5] : ~ q(c),
    file('Problems/PRV010+1.p',s2) ).

fof(s3,axiom,
    f(g(c,a)) = b,
    file('Problems/PRV010+1.p',s3) ).

fof(s4,axiom,
    ( ! [X6,X7] :
      ? [X8] : X7 = a
    & p(a) ),
    file('Problems/PRV010+1.p',s4) ).

fof(c,conjecture,
    ( ? [X22] : X22 = X22
    | ! [X23] :
      ? [X24] :
      ! [X25] :
      ? [X26] : q(a) ),
    file('Problems/PRV010+1.p',c) ).

fof(s5,plain,
    ( q(b)
    | ~ q(b) ),
    inference(excluded_middle,[status(thm)],[s2]) ).

fof(s6,plain,
    ~ ~ ( q(b)
        | ~ q(b) ),
    inference(double_negation,[status(thm)],[s5]) ).

fof(s7,plain,
    ? [X5] : ~ q(c),
    inference(instantiate,[status(thm)],[s2]) ).

fof(s8,plain,
    ( r(g(a,g(c,a)),f(f(c)))
   => ! [X4] :
      ? [X5] : ~ q(c) ),
    inference(add_hypothesis,[status(thm)],[s2]) ).

fof(s9,plain,
    ~ ~ ! [X0,X2] :
        ? [X1] : t,
    inference(double_negation,[status(thm)],[s0]) ).

fof(s10,plain,
    ? [X9] :
      ( q(X9)
      | ~ q(X9) ),
    inference(existential_gen,[status(thm)],[s5]) ).

fof(s11,plain,
    ! [X0,X2] :
    ? [X1] : t,
    inference(remove_double_negation,[status(thm)],[s9]) ).

fof(s12,plain,
    ? [X10] : f(g(X10,a)) = b,
    inference(existential_gen,[status(thm)],[s3]) ).

fof(s13,plain,
    ! [X2] :
    ? [X1] : t,
    inference(instantiate,[status(thm)],[s0]) ).

fof(s14,plain,
    ? [X1] : t,
    inference(instantiate,[status(thm)],[s13]) ).

fof(s15,plain,
    t,
    inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X1,sK0)],[s14]) ).

fof(s16,plain,
    ( ! [X2] :
      ? [X1] : t
    & ! [X4] :
      ? [X5] : ~ q(c) ),
    inference(conjunction,[status(thm)],[s13,s2]) ).

fof(s17,plain,
    a = a,
    inference(reflexivity,[status(thm)],[s2]) ).

fof(s18,plain,
    ? [X11] :
      ( ! [X2] :
        ? [X1] : t
      & ! [X4] :
        ? [X5] : ~ q(X11) ),
    inference(existential_gen,[status(thm)],[s16]) ).

fof(s19,plain,
    ! [X2] :
    ? [X1] : t,
    inference(split_conjunct,[status(thm)],[s16]) ).

fof(s20,plain,
    ! [X2] :
    ? [X1] : t,
    inference(instantiate,[status(thm)],[s11]) ).

fof(s21,plain,
    ? [X12] :
      ( q(X12)
      | ~ q(X12) ),
    inference(existential_gen,[status(thm)],[s5]) ).

fof(s22,plain,
    ? [X13,X5] : ~ q(X13),
    inference(existential_gen,[status(thm)],[s7]) ).

fof(s23,plain,
    ! [X4] : ~ q(c),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X5,sK1(X4))],[s2]) ).

fof(s24,plain,
    ? [X14] : f(g(X14,a)) = b,
    inference(existential_gen,[status(thm)],[s3]) ).

fof(s25,plain,
    ? [X15] :
      ( q(X15)
      | ~ q(X15) ),
    inference(rename_variable,[status(thm)],[s10]) ).

fof(s26,plain,
    p(a),
    inference(split_conjunct,[status(thm)],[s4]) ).

fof(s27,plain,
    ? [X16] : f(g(X16,a)) = b,
    inference(existential_gen,[status(thm)],[s3]) ).

fof(s28,plain,
    ! [X4] :
    ? [X5] : ~ q(c),
    inference(split_conjunct,[status(thm)],[s16]) ).

fof(s29,plain,
    ? [X17] :
    ! [X4] :
    ? [X5] : ~ q(X17),
    inference(existential_gen,[status(thm)],[s2]) ).

fof(s30,plain,
    p(a),
    inference(split_conjunct,[status(thm)],[s4]) ).

fof(s31,plain,
    ? [X18] : X18 = X18,
    inference(existential_gen,[status(thm)],[s17]) ).

fof(s32,plain,
    ( ~ ! [X19] :
        ? [X20] : p(X19)
    | ~ ~ ! [X19] :
          ? [X20] : p(X19) ),
    inference(excluded_middle,[status(thm)],[s13]) ).

fof(s33,plain,
    ! [X2] :
    ? [X1] : t,
    inference(split_conjunct,[status(thm)],[s16]) ).

fof(s34,plain,
    ( ! [X0,X2] :
      ? [X1] : t
    | a = b ),
    inference(weaken,[status(thm)],[s11]) ).

fof(s35,plain,
    ? [X21] :
    ! [X3] :
      ( X3 = X21
    <=> ( t
        | q(f(X3)) ) ),
    inference(existential_gen,[status(thm)],[s1]) ).

fof(s36,plain,
    ? [X22] : X22 = X22,
    inference(rename_variable,[status(thm)],[s31]) ).

fof(s37,plain,
    ! [X2] :
    ? [X1] : t,
    inference(instantiate,[status(thm),new_symbols(herbrand,[m0])],[s0]) ).

fof(s38,plain,
    ( ~ q(b)
    | q(b) ),
    inference(commute,[status(thm)],[s5]) ).

fof(s39,plain,
    ( b = a
  <=> ( t
      | q(f(b)) ) ),
    inference(instantiate,[status(thm)],[s1]) ).

fof(s40,plain,
    ( g(g(a,a),g(b,a)) = f(g(a,a))
   => ( q(b)
      | ~ q(b) ) ),
    inference(add_hypothesis,[status(thm)],[s5]) ).

fof(s41,plain,
    p(a),
    inference(split_conjunct,[status(thm)],[s4]) ).

fof(s42,plain,
    ! [X4] :
    ? [X5] : ~ q(sK2),
    inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X17,sK2)],[s29]) ).

fof(s43,plain,
    a = a,
    inference(reflexivity,[status(thm)],[s38]) ).

fof(s44,plain,
    ( a = b
    | ! [X0,X2] :
      ? [X1] : t ),
    inference(commute,[status(thm)],[s34]) ).

fof(s45,plain,
    ( ? [X22] : X22 = X22
    | ! [X23] :
      ? [X24] :
      ! [X25] :
      ? [X26] : q(a) ),
    inference(weaken,[status(thm)],[s36]) ).

fof(negc,negated_conjecture,
    ~ ( ? [X22] : X22 = X22
      | ! [X23] :
        ? [X24] :
        ! [X25] :
        ? [X26] : q(a) ),
    inference(negated_conjecture,[status(cth)],[c]) ).

fof(bot,plain,
    $false,
    inference(consequence,[status(thm)],[negc,s45]) ).

% SZS output end Proof
