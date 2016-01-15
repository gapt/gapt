%------------------------------------------------------------------------------
% File       : SPASS---3.7
% Problem    : HEN005-6 : TPTP v6.0.0. Released v1.0.0.
% Transform  : none
% Format     : tptp
% Command    : run_spass %d %s

% Computer   : n035.star.cs.uiowa.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2609 0 2.40GHz
% Memory     : 32286.75MB
% OS         : Linux 2.6.32-431.1.2.el6.x86_64
% CPULimit   : 300s
% DateTime   : Fri Apr  4 04:18:16 EDT 2014

% Result     : Unsatisfiable 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of clauses        :   36 (  66 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   19
%              Number of atoms          :   58 ( 114 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(2,axiom,
    ( equal(divide(zero,U),zero) ),
    file('HEN005-6.p',unknown),
    []).

cnf(3,axiom,
    ( less_equal(a,b) ),
    file('HEN005-6.p',unknown),
    []).

cnf(4,axiom,
    ( less_equal(b,c) ),
    file('HEN005-6.p',unknown),
    []).

cnf(5,axiom,
    ( ~ less_equal(a,c) ),
    file('HEN005-6.p',unknown),
    []).

cnf(6,axiom,
    ( ~ less_equal(U,V)
    | equal(divide(U,V),zero) ),
    file('HEN005-6.p',unknown),
    []).

cnf(7,axiom,
    ( ~ equal(divide(U,V),zero)
    | less_equal(U,V) ),
    file('HEN005-6.p',unknown),
    []).

cnf(8,axiom,
    ( less_equal(divide(U,V),U) ),
    file('HEN005-6.p',unknown),
    []).

cnf(9,axiom,
    ( less_equal(divide(divide(U,V),divide(W,V)),divide(divide(U,W),V)) ),
    file('HEN005-6.p',unknown),
    []).

cnf(10,axiom,
    ( less_equal(zero,U) ),
    file('HEN005-6.p',unknown),
    []).

cnf(11,axiom,
    ( ~ less_equal(U,V)
    | ~ less_equal(V,U)
    | equal(V,U) ),
    file('HEN005-6.p',unknown),
    []).

cnf(13,plain,
    ( ~ equal(divide(a,c),zero) ),
    inference(res,[status(thm),theory(equality)],[7,5]),
    [iquote('0:Res:7.1,5.0')]).

cnf(32,plain,
    ( ~ less_equal(U,zero)
    | equal(U,zero) ),
    inference(res,[status(thm),theory(equality)],[10,11]),
    [iquote('0:Res:10.0,11.0')]).

cnf(33,plain,
    ( ~ less_equal(U,divide(U,V))
    | equal(divide(U,V),U) ),
    inference(res,[status(thm),theory(equality)],[8,11]),
    [iquote('0:Res:8.0,11.0')]).

cnf(37,plain,
    ( ~ less_equal(U,V)
    | less_equal(divide(divide(U,W),divide(V,W)),divide(zero,W)) ),
    inference(spr,[status(thm),theory(equality)],[6,9]),
    [iquote('0:SpR:6.1,9.0')]).

cnf(40,plain,
    ( less_equal(divide(divide(U,V),zero),divide(divide(U,zero),V)) ),
    inference(spr,[status(thm),theory(equality)],[2,9]),
    [iquote('0:SpR:2.0,9.0')]).

cnf(53,plain,
    ( ~ less_equal(U,V)
    | less_equal(divide(divide(U,W),divide(V,W)),zero) ),
    inference(rew,[status(thm),theory(equality)],[2,37]),
    [iquote('0:Rew:2.0,37.1')]).

cnf(91,plain,
    ( ~ less_equal(divide(U,zero),V)
    | less_equal(divide(divide(U,V),zero),zero) ),
    inference(spr,[status(thm),theory(equality)],[6,40]),
    [iquote('0:SpR:6.1,40.0')]).

cnf(235,plain,
    ( ~ less_equal(U,V)
    | equal(divide(divide(U,W),divide(V,W)),zero) ),
    inference(res,[status(thm),theory(equality)],[53,32]),
    [iquote('0:Res:53.1,32.0')]).

cnf(732,plain,
    ( ~ less_equal(divide(U,zero),V)
    | equal(divide(divide(U,V),zero),zero) ),
    inference(res,[status(thm),theory(equality)],[91,32]),
    [iquote('0:Res:91.1,32.0')]).

cnf(919,plain,
    ( ~ less_equal(U,V)
    | ~ less_equal(W,U)
    | equal(divide(divide(W,V),zero),zero) ),
    inference(spr,[status(thm),theory(equality)],[6,235]),
    [iquote('0:SpR:6.1,235.1')]).

cnf(2036,plain,
    ( ~ less_equal(divide(U,zero),V)
    | ~ equal(zero,zero)
    | less_equal(divide(U,V),zero) ),
    inference(spl,[status(thm),theory(equality)],[732,7]),
    [iquote('0:SpL:732.1,7.0')]).

cnf(2061,plain,
    ( ~ less_equal(divide(U,zero),V)
    | less_equal(divide(U,V),zero) ),
    inference(obv,[status(thm),theory(equality)],[2036]),
    [iquote('0:Obv:2036.1')]).

cnf(2102,plain,
    ( less_equal(divide(U,U),zero) ),
    inference(res,[status(thm),theory(equality)],[8,2061]),
    [iquote('0:Res:8.0,2061.0')]).

cnf(2128,plain,
    ( equal(divide(U,U),zero) ),
    inference(res,[status(thm),theory(equality)],[2102,32]),
    [iquote('0:Res:2102.0,32.0')]).

cnf(2184,plain,
    ( ~ equal(zero,zero)
    | less_equal(U,U) ),
    inference(spl,[status(thm),theory(equality)],[2128,7]),
    [iquote('0:SpL:2128.0,7.0')]).

cnf(2208,plain,
    ( less_equal(U,U) ),
    inference(obv,[status(thm),theory(equality)],[2184]),
    [iquote('0:Obv:2184.0')]).

cnf(2251,plain,
    ( less_equal(divide(U,divide(U,zero)),zero) ),
    inference(res,[status(thm),theory(equality)],[2208,2061]),
    [iquote('0:Res:2208.0,2061.0')]).

cnf(2390,plain,
    ( equal(divide(U,divide(U,zero)),zero) ),
    inference(res,[status(thm),theory(equality)],[2251,32]),
    [iquote('0:Res:2251.0,32.0')]).

cnf(2454,plain,
    ( ~ equal(zero,zero)
    | less_equal(U,divide(U,zero)) ),
    inference(spl,[status(thm),theory(equality)],[2390,7]),
    [iquote('0:SpL:2390.0,7.0')]).

cnf(2473,plain,
    ( less_equal(U,divide(U,zero)) ),
    inference(obv,[status(thm),theory(equality)],[2454]),
    [iquote('0:Obv:2454.0')]).

cnf(2518,plain,
    ( equal(divide(U,zero),U) ),
    inference(res,[status(thm),theory(equality)],[2473,33]),
    [iquote('0:Res:2473.0,33.0')]).

cnf(2632,plain,
    ( ~ less_equal(U,V)
    | ~ less_equal(W,U)
    | equal(divide(W,V),zero) ),
    inference(rew,[status(thm),theory(equality)],[2518,919]),
    [iquote('0:Rew:2518.0,919.2')]).

cnf(3658,plain,
    ( ~ less_equal(U,b)
    | equal(divide(U,c),zero) ),
    inference(res,[status(thm),theory(equality)],[4,2632]),
    [iquote('0:Res:4.0,2632.0')]).

cnf(3716,plain,
    ( ~ less_equal(a,b)
    | ~ equal(zero,zero) ),
    inference(spl,[status(thm),theory(equality)],[3658,13]),
    [iquote('0:SpL:3658.1,13.0')]).

cnf(3720,plain,
    ( ~ less_equal(a,b) ),
    inference(obv,[status(thm),theory(equality)],[3716]),
    [iquote('0:Obv:3716.1')]).

cnf(3721,plain,
    ( $false ),
    inference(mrr,[status(thm)],[3720,3]),
    [iquote('0:MRR:3720.0,3.0')]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% % Problem    : HEN005-6 : TPTP v6.0.0. Released v1.0.0.
% % Command    : run_spass %d %s
% % Computer   : n035.star.cs.uiowa.edu
% % Model      : x86_64 x86_64
% % CPU        : Intel(R) Xeon(R) CPU E5-2609 0 @ 2.40GHz
% % Memory     : 32286.75MB
% % OS         : Linux 2.6.32-431.1.2.el6.x86_64
% % CPULimit   : 300
% % DateTime   : Wed Apr  2 14:02:30 CDT 2014
% % CPUTime    : 1.21 
% 
% SPASS V 3.7 
% SPASS beiseite: Proof found.
% % SZS status Theorem
% Problem: /export/starexec/sandbox/benchmark/HEN005-6.p 
% SPASS derived 2524 clauses, backtracked 0 clauses, performed 0 splits and kept 480 clauses.
% SPASS allocated 21911 KBytes.
% SPASS spent	0:00:00.14 on the problem.
% 0:00:00.01 for the input.
% 0:00:00.00 for the FLOTTER CNF translation.
% 0:00:00.01 for inferences.
% 0:00:00.00 for the backtracking.
% 0:00:00.11 for the reduction.
% 
% 
% Here is a proof with depth 11, length 36 :
% % SZS output start Refutation
% 2[0:Inp] ||  -> equal(divide(zero,U),zero)**.
% 3[0:Inp] ||  -> less_equal(a,b)*.
% 4[0:Inp] ||  -> less_equal(b,c)*.
% 5[0:Inp] || less_equal(a,c)* -> .
% 6[0:Inp] || less_equal(U,V) -> equal(divide(U,V),zero)**.
% 7[0:Inp] || equal(divide(U,V),zero)** -> less_equal(U,V).
% 8[0:Inp] ||  -> less_equal(divide(U,V),U)*.
% 9[0:Inp] ||  -> less_equal(divide(divide(U,V),divide(W,V)),divide(divide(U,W),V))*.
% 10[0:Inp] ||  -> less_equal(zero,U)*.
% 11[0:Inp] || less_equal(U,V)*+ less_equal(V,U)* -> equal(V,U).
% 13[0:Res:7.1,5.0] || equal(divide(a,c),zero)** -> .
% 32[0:Res:10.0,11.0] || less_equal(U,zero)* -> equal(U,zero).
% 33[0:Res:8.0,11.0] || less_equal(U,divide(U,V))* -> equal(divide(U,V),U).
% 37[0:SpR:6.1,9.0] || less_equal(U,V) -> less_equal(divide(divide(U,W),divide(V,W)),divide(zero,W))*.
% 40[0:SpR:2.0,9.0] ||  -> less_equal(divide(divide(U,V),zero),divide(divide(U,zero),V))*.
% 53[0:Rew:2.0,37.1] || less_equal(U,V) -> less_equal(divide(divide(U,W),divide(V,W)),zero)*.
% 91[0:SpR:6.1,40.0] || less_equal(divide(U,zero),V) -> less_equal(divide(divide(U,V),zero),zero)*.
% 235[0:Res:53.1,32.0] || less_equal(U,V) -> equal(divide(divide(U,W),divide(V,W)),zero)**.
% 732[0:Res:91.1,32.0] || less_equal(divide(U,zero),V) -> equal(divide(divide(U,V),zero),zero)**.
% 919[0:SpR:6.1,235.1] || less_equal(U,V)* less_equal(W,U)* -> equal(divide(divide(W,V),zero),zero)**.
% 2036[0:SpL:732.1,7.0] || less_equal(divide(U,zero),V)* equal(zero,zero) -> less_equal(divide(U,V),zero)*.
% 2061[0:Obv:2036.1] || less_equal(divide(U,zero),V)*+ -> less_equal(divide(U,V),zero)*.
% 2102[0:Res:8.0,2061.0] ||  -> less_equal(divide(U,U),zero)*.
% 2128[0:Res:2102.0,32.0] ||  -> equal(divide(U,U),zero)**.
% 2184[0:SpL:2128.0,7.0] || equal(zero,zero) -> less_equal(U,U)*.
% 2208[0:Obv:2184.0] ||  -> less_equal(U,U)*.
% 2251[0:Res:2208.0,2061.0] ||  -> less_equal(divide(U,divide(U,zero)),zero)*.
% 2390[0:Res:2251.0,32.0] ||  -> equal(divide(U,divide(U,zero)),zero)**.
% 2454[0:SpL:2390.0,7.0] || equal(zero,zero) -> less_equal(U,divide(U,zero))*.
% 2473[0:Obv:2454.0] ||  -> less_equal(U,divide(U,zero))*.
% 2518[0:Res:2473.0,33.0] ||  -> equal(divide(U,zero),U)**.
% 2632[0:Rew:2518.0,919.2] || less_equal(U,V)*+ less_equal(W,U)* -> equal(divide(W,V),zero)**.
% 3658[0:Res:4.0,2632.0] || less_equal(U,b) -> equal(divide(U,c),zero)**.
% 3716[0:SpL:3658.1,13.0] || less_equal(a,b)* equal(zero,zero) -> .
% 3720[0:Obv:3716.1] || less_equal(a,b)* -> .
% 3721[0:MRR:3720.0,3.0] ||  -> .
% % SZS output end Refutation
% Formulae used in the proof : zero_divide_anything_is_zero a_LE_b b_LE_c prove_a_LE_c quotient_less_equal1 quotient_less_equal2 quotient_smaller_than_numerator quotient_property zero_is_smallest less_equal_and_equal
% 
% 
% EOF
%------------------------------------------------------------------------------
