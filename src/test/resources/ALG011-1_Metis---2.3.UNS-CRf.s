%------------------------------------------------------------------------------
% File       : Metis---2.3
% Problem    : ALG011-1 : TPTP v6.1.0. Released v2.7.0.
% Transform  : none
% Format     : tptp:raw
% Command    : metis --show proof --show saturation %s

% Computer   : n064.star.cs.uiowa.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2609 0 2.40GHz
% Memory     : 32286.75MB
% OS         : Linux 2.6.32-431.20.3.el6.x86_64
% CPULimit   : 300s
% DateTime   : Wed Aug 13 17:06:32 EDT 2014

% Result     : Unsatisfiable 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of clauses        :   65 ( 127 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  116 ( 233 expanded)
%              Number of equality atoms :   37 ( 120 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(f_is_associative,axiom,
    ( f(X,f(Y,Z)) = f(f(X,Y),Z) )).

cnf(partitions_union,axiom,
    ( c(X)
    | d(X) )).

cnf(partitions_exclusive,hypothesis,
    ( ~ c(X)
    | ~ d(X) )).

cnf(partition_c_not_empty,hypothesis,
    ( c(a1) )).

cnf(partition_d_not_empty,hypothesis,
    ( d(a2) )).

cnf(conjecture_1,negated_conjecture,
    ( d(f(X,Y))
    | ~ c(X)
    | ~ c(Y) )).

cnf(conjecture_2,negated_conjecture,
    ( c(f(X,Y))
    | ~ d(X)
    | ~ d(Y) )).

cnf(refute_0_0,plain,
    ( ~ d(f(a2,f(a1,a1)))
    | c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))) ),
    inference(subst,[],[conjecture_2:[bind(X,$fot(f(a2,f(a1,a1)))),bind(Y,$fot(f(a2,f(a1,a1))))]])).

cnf(refute_0_1,plain,
    ( ~ c(X_9)
    | ~ c(a1)
    | d(f(X_9,a1)) ),
    inference(subst,[],[conjecture_1:[bind(X,$fot(X_9)),bind(Y,$fot(a1))]])).

cnf(refute_0_2,plain,
    ( ~ c(X_9)
    | d(f(X_9,a1)) ),
    inference(resolve,[$cnf(c(a1))],[partition_c_not_empty,refute_0_1])).

cnf(refute_0_3,plain,
    ( ~ c(f(a2,a1))
    | d(f(f(a2,a1),a1)) ),
    inference(subst,[],[refute_0_2:[bind(X_9,$fot(f(a2,a1)))]])).

cnf(refute_0_4,plain,
    ( ~ c(f(a2,f(a2,a1)))
    | ~ d(f(a2,f(a2,a1))) ),
    inference(subst,[],[partitions_exclusive:[bind(X,$fot(f(a2,f(a2,a1))))]])).

cnf(refute_0_5,plain,
    ( ~ d(a2)
    | c(f(a2,a2)) ),
    inference(subst,[],[conjecture_2:[bind(X,$fot(a2)),bind(Y,$fot(a2))]])).

cnf(refute_0_6,plain,
    ( c(f(a2,a2)) ),
    inference(resolve,[$cnf(d(a2))],[partition_d_not_empty,refute_0_5])).

cnf(refute_0_7,plain,
    ( ~ c(f(a2,a2))
    | d(f(f(a2,a2),a1)) ),
    inference(subst,[],[refute_0_2:[bind(X_9,$fot(f(a2,a2)))]])).

cnf(refute_0_8,plain,
    ( d(f(f(a2,a2),a1)) ),
    inference(resolve,[$cnf(c(f(a2,a2)))],[refute_0_6,refute_0_7])).

cnf(refute_0_9,plain,
    ( X0 = X0 ),
    introduced(tautology,[refl,[$fot(X0)]])).

cnf(refute_0_10,plain,
    ( X0 != X0
    | X0 != Y0
    | Y0 = X0 ),
    introduced(tautology,[equality,[$cnf($equal(X0,X0)),[0],$fot(Y0)]])).

cnf(refute_0_11,plain,
    ( X0 != Y0
    | Y0 = X0 ),
    inference(resolve,[$cnf($equal(X0,X0))],[refute_0_9,refute_0_10])).

cnf(refute_0_12,plain,
    ( f(X,f(Y,Z)) != f(f(X,Y),Z)
    | f(f(X,Y),Z) = f(X,f(Y,Z)) ),
    inference(subst,[],[refute_0_11:[bind(X0,$fot(f(X,f(Y,Z)))),bind(Y0,$fot(f(f(X,Y),Z)))]])).

cnf(refute_0_13,plain,
    ( f(f(X,Y),Z) = f(X,f(Y,Z)) ),
    inference(resolve,[$cnf($equal(f(X,f(Y,Z)),f(f(X,Y),Z)))],[f_is_associative,refute_0_12])).

cnf(refute_0_14,plain,
    ( f(f(a2,a2),a1) = f(a2,f(a2,a1)) ),
    inference(subst,[],[refute_0_13:[bind(X,$fot(a2)),bind(Y,$fot(a2)),bind(Z,$fot(a1))]])).

cnf(refute_0_15,plain,
    ( f(f(a2,a2),a1) != f(a2,f(a2,a1))
    | ~ d(f(f(a2,a2),a1))
    | d(f(a2,f(a2,a1))) ),
    introduced(tautology,[equality,[$cnf(d(f(f(a2,a2),a1))),[0],$fot(f(a2,f(a2,a1)))]])).

cnf(refute_0_16,plain,
    ( ~ d(f(f(a2,a2),a1))
    | d(f(a2,f(a2,a1))) ),
    inference(resolve,[$cnf($equal(f(f(a2,a2),a1),f(a2,f(a2,a1))))],[refute_0_14,refute_0_15])).

cnf(refute_0_17,plain,
    ( d(f(a2,f(a2,a1))) ),
    inference(resolve,[$cnf(d(f(f(a2,a2),a1)))],[refute_0_8,refute_0_16])).

cnf(refute_0_18,plain,
    ( ~ c(f(a2,f(a2,a1))) ),
    inference(resolve,[$cnf(d(f(a2,f(a2,a1))))],[refute_0_17,refute_0_4])).

cnf(refute_0_19,plain,
    ( c(X_19)
    | d(X_19) ),
    inference(subst,[],[partitions_union:[bind(X,$fot(X_19))]])).

cnf(refute_0_20,plain,
    ( ~ d(X_18)
    | ~ d(a2)
    | c(f(a2,X_18)) ),
    inference(subst,[],[conjecture_2:[bind(X,$fot(a2)),bind(Y,$fot(X_18))]])).

cnf(refute_0_21,plain,
    ( ~ d(X_18)
    | c(f(a2,X_18)) ),
    inference(resolve,[$cnf(d(a2))],[partition_d_not_empty,refute_0_20])).

cnf(refute_0_22,plain,
    ( ~ d(X_19)
    | c(f(a2,X_19)) ),
    inference(subst,[],[refute_0_21:[bind(X_18,$fot(X_19))]])).

cnf(refute_0_23,plain,
    ( c(X_19)
    | c(f(a2,X_19)) ),
    inference(resolve,[$cnf(d(X_19))],[refute_0_19,refute_0_22])).

cnf(refute_0_24,plain,
    ( c(f(a2,a1))
    | c(f(a2,f(a2,a1))) ),
    inference(subst,[],[refute_0_23:[bind(X_19,$fot(f(a2,a1)))]])).

cnf(refute_0_25,plain,
    ( c(f(a2,a1)) ),
    inference(resolve,[$cnf(c(f(a2,f(a2,a1))))],[refute_0_24,refute_0_18])).

cnf(refute_0_26,plain,
    ( d(f(f(a2,a1),a1)) ),
    inference(resolve,[$cnf(c(f(a2,a1)))],[refute_0_25,refute_0_3])).

cnf(refute_0_27,plain,
    ( f(f(a2,a1),a1) = f(a2,f(a1,a1)) ),
    inference(subst,[],[refute_0_13:[bind(X,$fot(a2)),bind(Y,$fot(a1)),bind(Z,$fot(a1))]])).

cnf(refute_0_28,plain,
    ( f(f(a2,a1),a1) != f(a2,f(a1,a1))
    | ~ d(f(f(a2,a1),a1))
    | d(f(a2,f(a1,a1))) ),
    introduced(tautology,[equality,[$cnf(d(f(f(a2,a1),a1))),[0],$fot(f(a2,f(a1,a1)))]])).

cnf(refute_0_29,plain,
    ( ~ d(f(f(a2,a1),a1))
    | d(f(a2,f(a1,a1))) ),
    inference(resolve,[$cnf($equal(f(f(a2,a1),a1),f(a2,f(a1,a1))))],[refute_0_27,refute_0_28])).

cnf(refute_0_30,plain,
    ( d(f(a2,f(a1,a1))) ),
    inference(resolve,[$cnf(d(f(f(a2,a1),a1)))],[refute_0_26,refute_0_29])).

cnf(refute_0_31,plain,
    ( c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))) ),
    inference(resolve,[$cnf(d(f(a2,f(a1,a1))))],[refute_0_30,refute_0_0])).

cnf(refute_0_32,plain,
    ( f(f(a1,a1),f(a2,f(a1,a1))) = f(a1,f(a1,f(a2,f(a1,a1)))) ),
    inference(subst,[],[refute_0_13:[bind(X,$fot(a1)),bind(Y,$fot(a1)),bind(Z,$fot(f(a2,f(a1,a1))))]])).

cnf(refute_0_33,plain,
    ( f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) = f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) ),
    introduced(tautology,[refl,[$fot(f(a2,f(f(a1,a1),f(a2,f(a1,a1)))))]])).

cnf(refute_0_34,plain,
    ( f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) != f(a2,f(f(a1,a1),f(a2,f(a1,a1))))
    | f(f(a1,a1),f(a2,f(a1,a1))) != f(a1,f(a1,f(a2,f(a1,a1))))
    | f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    introduced(tautology,[equality,[$cnf($equal(f(a2,f(f(a1,a1),f(a2,f(a1,a1)))),f(a2,f(f(a1,a1),f(a2,f(a1,a1)))))),[1,1],$fot(f(a1,f(a1,f(a2,f(a1,a1)))))]])).

cnf(refute_0_35,plain,
    ( f(f(a1,a1),f(a2,f(a1,a1))) != f(a1,f(a1,f(a2,f(a1,a1))))
    | f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    inference(resolve,[$cnf($equal(f(a2,f(f(a1,a1),f(a2,f(a1,a1)))),f(a2,f(f(a1,a1),f(a2,f(a1,a1))))))],[refute_0_33,refute_0_34])).

cnf(refute_0_36,plain,
    ( f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    inference(resolve,[$cnf($equal(f(f(a1,a1),f(a2,f(a1,a1))),f(a1,f(a1,f(a2,f(a1,a1))))))],[refute_0_32,refute_0_35])).

cnf(refute_0_37,plain,
    ( f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) = f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) ),
    inference(subst,[],[refute_0_13:[bind(X,$fot(a2)),bind(Y,$fot(f(a1,a1))),bind(Z,$fot(f(a2,f(a1,a1))))]])).

cnf(refute_0_38,plain,
    ( Y0 != X0
    | Y0 != Z0
    | X0 = Z0 ),
    introduced(tautology,[equality,[$cnf($equal(Y0,Z0)),[0],$fot(X0)]])).

cnf(refute_0_39,plain,
    ( X0 != Y0
    | Y0 != Z0
    | X0 = Z0 ),
    inference(resolve,[$cnf($equal(Y0,X0))],[refute_0_11,refute_0_38])).

cnf(refute_0_40,plain,
    ( f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) != f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))
    | f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) != f(a2,f(f(a1,a1),f(a2,f(a1,a1))))
    | f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    inference(subst,[],[refute_0_39:[bind(X0,$fot(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))),bind(Y0,$fot(f(a2,f(f(a1,a1),f(a2,f(a1,a1)))))),bind(Z0,$fot(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))]])).

cnf(refute_0_41,plain,
    ( f(a2,f(f(a1,a1),f(a2,f(a1,a1)))) != f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))
    | f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    inference(resolve,[$cnf($equal(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))),f(a2,f(f(a1,a1),f(a2,f(a1,a1))))))],[refute_0_37,refute_0_40])).

cnf(refute_0_42,plain,
    ( f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) = f(a2,f(a1,f(a1,f(a2,f(a1,a1))))) ),
    inference(resolve,[$cnf($equal(f(a2,f(f(a1,a1),f(a2,f(a1,a1)))),f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))],[refute_0_36,refute_0_41])).

cnf(refute_0_43,plain,
    ( f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) != f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))
    | ~ c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))
    | c(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    introduced(tautology,[equality,[$cnf(c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))),[0],$fot(f(a2,f(a1,f(a1,f(a2,f(a1,a1))))))]])).

cnf(refute_0_44,plain,
    ( ~ c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))
    | c(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(resolve,[$cnf($equal(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))),f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))],[refute_0_42,refute_0_43])).

cnf(refute_0_45,plain,
    ( c(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(resolve,[$cnf(c(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))))],[refute_0_31,refute_0_44])).

cnf(refute_0_46,plain,
    ( ~ c(f(a2,f(a1,f(a1,f(a2,f(a1,a1))))))
    | ~ d(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(subst,[],[partitions_exclusive:[bind(X,$fot(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))]])).

cnf(refute_0_47,plain,
    ( ~ c(f(a2,f(a1,a1)))
    | d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))) ),
    inference(subst,[],[conjecture_1:[bind(X,$fot(f(a2,f(a1,a1)))),bind(Y,$fot(f(a2,f(a1,a1))))]])).

cnf(refute_0_48,plain,
    ( ~ c(a1)
    | d(f(a1,a1)) ),
    inference(subst,[],[conjecture_1:[bind(X,$fot(a1)),bind(Y,$fot(a1))]])).

cnf(refute_0_49,plain,
    ( d(f(a1,a1)) ),
    inference(resolve,[$cnf(c(a1))],[partition_c_not_empty,refute_0_48])).

cnf(refute_0_50,plain,
    ( ~ d(f(a1,a1))
    | c(f(a2,f(a1,a1))) ),
    inference(subst,[],[refute_0_21:[bind(X_18,$fot(f(a1,a1)))]])).

cnf(refute_0_51,plain,
    ( c(f(a2,f(a1,a1))) ),
    inference(resolve,[$cnf(d(f(a1,a1)))],[refute_0_49,refute_0_50])).

cnf(refute_0_52,plain,
    ( d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))) ),
    inference(resolve,[$cnf(c(f(a2,f(a1,a1))))],[refute_0_51,refute_0_47])).

cnf(refute_0_53,plain,
    ( f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) != f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))
    | ~ d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))
    | d(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    introduced(tautology,[equality,[$cnf(d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))),[0],$fot(f(a2,f(a1,f(a1,f(a2,f(a1,a1))))))]])).

cnf(refute_0_54,plain,
    ( ~ d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))))
    | d(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(resolve,[$cnf($equal(f(f(a2,f(a1,a1)),f(a2,f(a1,a1))),f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))],[refute_0_42,refute_0_53])).

cnf(refute_0_55,plain,
    ( d(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(resolve,[$cnf(d(f(f(a2,f(a1,a1)),f(a2,f(a1,a1)))))],[refute_0_52,refute_0_54])).

cnf(refute_0_56,plain,
    ( ~ c(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))) ),
    inference(resolve,[$cnf(d(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))],[refute_0_55,refute_0_46])).

cnf(refute_0_57,plain,
    ( $false ),
    inference(resolve,[$cnf(c(f(a2,f(a1,f(a1,f(a2,f(a1,a1)))))))],[refute_0_45,refute_0_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.02  % Problem    : ALG011-1 : TPTP v6.1.0. Released v2.7.0.
% 0.00/0.03  % Command    : metis --show proof --show saturation %s
% 0.00/1.05  % Computer   : n064.star.cs.uiowa.edu
% 0.00/1.05  % Model      : x86_64 x86_64
% 0.00/1.05  % CPU        : Intel(R) Xeon(R) CPU E5-2609 0 @ 2.40GHz
% 0.00/1.05  % Memory     : 32286.75MB
% 0.00/1.05  % OS         : Linux 2.6.32-431.20.3.el6.x86_64
% 0.00/1.05  % CPULimit   : 300
% 0.00/1.05  % DateTime   : Wed Aug  6 09:41:13 CDT 2014
% 0.00/1.06  % CPUTime    : 
% 0.00/1.06  ---------------------------------------------------------------------------
% 2.93/4.00  SZS status Unsatisfiable for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/4.00  
% 2.93/4.00  SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/4.00  cnf(f_is_associative, axiom, (f(X, f(Y, Z)) = f(f(X, Y), Z))).
% 2.93/4.00  
% 2.93/4.00  cnf(partitions_union, axiom, (c(X) | d(X))).
% 2.93/4.00  
% 2.93/4.00  cnf(partitions_exclusive, hypothesis, (~ c(X) | ~ d(X))).
% 2.93/4.00  
% 2.93/4.00  cnf(partition_c_not_empty, hypothesis, (c(a1))).
% 2.93/4.00  
% 2.93/4.00  cnf(partition_d_not_empty, hypothesis, (d(a2))).
% 2.93/4.00  
% 2.93/4.00  cnf(conjecture_1, negated_conjecture, (d(f(X, Y)) | ~ c(X) | ~ c(Y))).
% 2.93/4.00  
% 2.93/4.00  cnf(conjecture_2, negated_conjecture, (c(f(X, Y)) | ~ d(X) | ~ d(Y))).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_0, plain,
% 2.93/4.00      (~ d(f(a2, f(a1, a1))) | c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [conjecture_2 :
% 2.93/4.00                 [bind(X, $fot(f(a2, f(a1, a1)))),
% 2.93/4.00                  bind(Y, $fot(f(a2, f(a1, a1))))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_1, plain, (~ c(X_9) | ~ c(a1) | d(f(X_9, a1))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [conjecture_1 : [bind(X, $fot(X_9)), bind(Y, $fot(a1))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_2, plain, (~ c(X_9) | d(f(X_9, a1))),
% 2.93/4.00      inference(resolve, [$cnf(c(a1))],
% 2.93/4.00                [partition_c_not_empty, refute_0_1])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_3, plain, (~ c(f(a2, a1)) | d(f(f(a2, a1), a1))),
% 2.93/4.00      inference(subst, [], [refute_0_2 : [bind(X_9, $fot(f(a2, a1)))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_4, plain, (~ c(f(a2, f(a2, a1))) | ~ d(f(a2, f(a2, a1)))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [partitions_exclusive : [bind(X, $fot(f(a2, f(a2, a1))))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_5, plain, (~ d(a2) | c(f(a2, a2))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [conjecture_2 : [bind(X, $fot(a2)), bind(Y, $fot(a2))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_6, plain, (c(f(a2, a2))),
% 2.93/4.00      inference(resolve, [$cnf(d(a2))],
% 2.93/4.00                [partition_d_not_empty, refute_0_5])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_7, plain, (~ c(f(a2, a2)) | d(f(f(a2, a2), a1))),
% 2.93/4.00      inference(subst, [], [refute_0_2 : [bind(X_9, $fot(f(a2, a2)))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_8, plain, (d(f(f(a2, a2), a1))),
% 2.93/4.00      inference(resolve, [$cnf(c(f(a2, a2)))], [refute_0_6, refute_0_7])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_9, plain, (X0 = X0),
% 2.93/4.00      introduced(tautology, [refl, [$fot(X0)]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_10, plain, (X0 != X0 | X0 != Y0 | Y0 = X0),
% 2.93/4.00      introduced(tautology,
% 2.93/4.00                 [equality, [$cnf($equal(X0, X0)), [0], $fot(Y0)]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_11, plain, (X0 != Y0 | Y0 = X0),
% 2.93/4.00      inference(resolve, [$cnf($equal(X0, X0))], [refute_0_9, refute_0_10])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_12, plain,
% 2.93/4.00      (f(X, f(Y, Z)) != f(f(X, Y), Z) | f(f(X, Y), Z) = f(X, f(Y, Z))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [refute_0_11 :
% 2.93/4.00                 [bind(X0, $fot(f(X, f(Y, Z)))),
% 2.93/4.00                  bind(Y0, $fot(f(f(X, Y), Z)))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_13, plain, (f(f(X, Y), Z) = f(X, f(Y, Z))),
% 2.93/4.00      inference(resolve, [$cnf($equal(f(X, f(Y, Z)), f(f(X, Y), Z)))],
% 2.93/4.00                [f_is_associative, refute_0_12])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_14, plain, (f(f(a2, a2), a1) = f(a2, f(a2, a1))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [refute_0_13 :
% 2.93/4.00                 [bind(X, $fot(a2)), bind(Y, $fot(a2)),
% 2.93/4.00                  bind(Z, $fot(a1))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_15, plain,
% 2.93/4.00      (f(f(a2, a2), a1) != f(a2, f(a2, a1)) | ~ d(f(f(a2, a2), a1)) |
% 2.93/4.00       d(f(a2, f(a2, a1)))),
% 2.93/4.00      introduced(tautology,
% 2.93/4.00                 [equality,
% 2.93/4.00                  [$cnf(d(f(f(a2, a2), a1))), [0],
% 2.93/4.00                   $fot(f(a2, f(a2, a1)))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_16, plain, (~ d(f(f(a2, a2), a1)) | d(f(a2, f(a2, a1)))),
% 2.93/4.00      inference(resolve, [$cnf($equal(f(f(a2, a2), a1), f(a2, f(a2, a1))))],
% 2.93/4.00                [refute_0_14, refute_0_15])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_17, plain, (d(f(a2, f(a2, a1)))),
% 2.93/4.00      inference(resolve, [$cnf(d(f(f(a2, a2), a1)))],
% 2.93/4.00                [refute_0_8, refute_0_16])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_18, plain, (~ c(f(a2, f(a2, a1)))),
% 2.93/4.00      inference(resolve, [$cnf(d(f(a2, f(a2, a1))))],
% 2.93/4.00                [refute_0_17, refute_0_4])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_19, plain, (c(X_19) | d(X_19)),
% 2.93/4.00      inference(subst, [], [partitions_union : [bind(X, $fot(X_19))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_20, plain, (~ d(X_18) | ~ d(a2) | c(f(a2, X_18))),
% 2.93/4.00      inference(subst, [],
% 2.93/4.00                [conjecture_2 : [bind(X, $fot(a2)), bind(Y, $fot(X_18))]])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_21, plain, (~ d(X_18) | c(f(a2, X_18))),
% 2.93/4.00      inference(resolve, [$cnf(d(a2))],
% 2.93/4.00                [partition_d_not_empty, refute_0_20])).
% 2.93/4.00  
% 2.93/4.00  cnf(refute_0_22, plain, (~ d(X_19) | c(f(a2, X_19))),
% 2.93/4.00      inference(subst, [], [refute_0_21 : [bind(X_18, $fot(X_19))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_23, plain, (c(X_19) | c(f(a2, X_19))),
% 2.93/4.01      inference(resolve, [$cnf(d(X_19))], [refute_0_19, refute_0_22])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_24, plain, (c(f(a2, a1)) | c(f(a2, f(a2, a1)))),
% 2.93/4.01      inference(subst, [], [refute_0_23 : [bind(X_19, $fot(f(a2, a1)))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_25, plain, (c(f(a2, a1))),
% 2.93/4.01      inference(resolve, [$cnf(c(f(a2, f(a2, a1))))],
% 2.93/4.01                [refute_0_24, refute_0_18])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_26, plain, (d(f(f(a2, a1), a1))),
% 2.93/4.01      inference(resolve, [$cnf(c(f(a2, a1)))], [refute_0_25, refute_0_3])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_27, plain, (f(f(a2, a1), a1) = f(a2, f(a1, a1))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [refute_0_13 :
% 2.93/4.01                 [bind(X, $fot(a2)), bind(Y, $fot(a1)),
% 2.93/4.01                  bind(Z, $fot(a1))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_28, plain,
% 2.93/4.01      (f(f(a2, a1), a1) != f(a2, f(a1, a1)) | ~ d(f(f(a2, a1), a1)) |
% 2.93/4.01       d(f(a2, f(a1, a1)))),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [equality,
% 2.93/4.01                  [$cnf(d(f(f(a2, a1), a1))), [0],
% 2.93/4.01                   $fot(f(a2, f(a1, a1)))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_29, plain, (~ d(f(f(a2, a1), a1)) | d(f(a2, f(a1, a1)))),
% 2.93/4.01      inference(resolve, [$cnf($equal(f(f(a2, a1), a1), f(a2, f(a1, a1))))],
% 2.93/4.01                [refute_0_27, refute_0_28])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_30, plain, (d(f(a2, f(a1, a1)))),
% 2.93/4.01      inference(resolve, [$cnf(d(f(f(a2, a1), a1)))],
% 2.93/4.01                [refute_0_26, refute_0_29])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_31, plain, (c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))),
% 2.93/4.01      inference(resolve, [$cnf(d(f(a2, f(a1, a1))))],
% 2.93/4.01                [refute_0_30, refute_0_0])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_32, plain,
% 2.93/4.01      (f(f(a1, a1), f(a2, f(a1, a1))) = f(a1, f(a1, f(a2, f(a1, a1))))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [refute_0_13 :
% 2.93/4.01                 [bind(X, $fot(a1)), bind(Y, $fot(a1)),
% 2.93/4.01                  bind(Z, $fot(f(a2, f(a1, a1))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_33, plain,
% 2.93/4.01      (f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) =
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1))))),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [refl, [$fot(f(a2, f(f(a1, a1), f(a2, f(a1, a1)))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_34, plain,
% 2.93/4.01      (f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) !=
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) |
% 2.93/4.01       f(f(a1, a1), f(a2, f(a1, a1))) != f(a1, f(a1, f(a2, f(a1, a1)))) |
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [equality,
% 2.93/4.01                  [$cnf($equal(f(a2, f(f(a1, a1), f(a2, f(a1, a1)))),
% 2.93/4.01                          f(a2, f(f(a1, a1), f(a2, f(a1, a1)))))), [1, 1],
% 2.93/4.01                   $fot(f(a1, f(a1, f(a2, f(a1, a1)))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_35, plain,
% 2.93/4.01      (f(f(a1, a1), f(a2, f(a1, a1))) != f(a1, f(a1, f(a2, f(a1, a1)))) |
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(a2, f(f(a1, a1), f(a2, f(a1, a1)))),
% 2.93/4.01                        f(a2, f(f(a1, a1), f(a2, f(a1, a1))))))],
% 2.93/4.01                [refute_0_33, refute_0_34])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_36, plain,
% 2.93/4.01      (f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(f(a1, a1), f(a2, f(a1, a1))),
% 2.93/4.01                        f(a1, f(a1, f(a2, f(a1, a1))))))],
% 2.93/4.01                [refute_0_32, refute_0_35])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_37, plain,
% 2.93/4.01      (f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) =
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1))))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [refute_0_13 :
% 2.93/4.01                 [bind(X, $fot(a2)), bind(Y, $fot(f(a1, a1))),
% 2.93/4.01                  bind(Z, $fot(f(a2, f(a1, a1))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_38, plain, (Y0 != X0 | Y0 != Z0 | X0 = Z0),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [equality, [$cnf($equal(Y0, Z0)), [0], $fot(X0)]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_39, plain, (X0 != Y0 | Y0 != Z0 | X0 = Z0),
% 2.93/4.01      inference(resolve, [$cnf($equal(Y0, X0))],
% 2.93/4.01                [refute_0_11, refute_0_38])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_40, plain,
% 2.93/4.01      (f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) !=
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1))))) |
% 2.93/4.01       f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) !=
% 2.93/4.01       f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) |
% 2.93/4.01       f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [refute_0_39 :
% 2.93/4.01                 [bind(X0, $fot(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))),
% 2.93/4.01                  bind(Y0, $fot(f(a2, f(f(a1, a1), f(a2, f(a1, a1)))))),
% 2.93/4.01                  bind(Z0, $fot(f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_41, plain,
% 2.93/4.01      (f(a2, f(f(a1, a1), f(a2, f(a1, a1)))) !=
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1))))) |
% 2.93/4.01       f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))),
% 2.93/4.01                        f(a2, f(f(a1, a1), f(a2, f(a1, a1))))))],
% 2.93/4.01                [refute_0_37, refute_0_40])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_42, plain,
% 2.93/4.01      (f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) =
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(a2, f(f(a1, a1), f(a2, f(a1, a1)))),
% 2.93/4.01                        f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))],
% 2.93/4.01                [refute_0_36, refute_0_41])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_43, plain,
% 2.93/4.01      (f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) !=
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1))))) |
% 2.93/4.01       ~ c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))) |
% 2.93/4.01       c(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [equality,
% 2.93/4.01                  [$cnf(c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))), [0],
% 2.93/4.01                   $fot(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_44, plain,
% 2.93/4.01      (~ c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))) |
% 2.93/4.01       c(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))),
% 2.93/4.01                        f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))],
% 2.93/4.01                [refute_0_42, refute_0_43])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_45, plain, (c(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(resolve, [$cnf(c(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))))],
% 2.93/4.01                [refute_0_31, refute_0_44])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_46, plain,
% 2.93/4.01      (~ c(f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))) |
% 2.93/4.01       ~ d(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [partitions_exclusive :
% 2.93/4.01                 [bind(X, $fot(f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_47, plain,
% 2.93/4.01      (~ c(f(a2, f(a1, a1))) | d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [conjecture_1 :
% 2.93/4.01                 [bind(X, $fot(f(a2, f(a1, a1)))),
% 2.93/4.01                  bind(Y, $fot(f(a2, f(a1, a1))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_48, plain, (~ c(a1) | d(f(a1, a1))),
% 2.93/4.01      inference(subst, [],
% 2.93/4.01                [conjecture_1 : [bind(X, $fot(a1)), bind(Y, $fot(a1))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_49, plain, (d(f(a1, a1))),
% 2.93/4.01      inference(resolve, [$cnf(c(a1))],
% 2.93/4.01                [partition_c_not_empty, refute_0_48])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_50, plain, (~ d(f(a1, a1)) | c(f(a2, f(a1, a1)))),
% 2.93/4.01      inference(subst, [], [refute_0_21 : [bind(X_18, $fot(f(a1, a1)))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_51, plain, (c(f(a2, f(a1, a1)))),
% 2.93/4.01      inference(resolve, [$cnf(d(f(a1, a1)))], [refute_0_49, refute_0_50])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_52, plain, (d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))),
% 2.93/4.01      inference(resolve, [$cnf(c(f(a2, f(a1, a1))))],
% 2.93/4.01                [refute_0_51, refute_0_47])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_53, plain,
% 2.93/4.01      (f(f(a2, f(a1, a1)), f(a2, f(a1, a1))) !=
% 2.93/4.01       f(a2, f(a1, f(a1, f(a2, f(a1, a1))))) |
% 2.93/4.01       ~ d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))) |
% 2.93/4.01       d(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      introduced(tautology,
% 2.93/4.01                 [equality,
% 2.93/4.01                  [$cnf(d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))))), [0],
% 2.93/4.01                   $fot(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))]])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_54, plain,
% 2.93/4.01      (~ d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))) |
% 2.93/4.01       d(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(resolve,
% 2.93/4.01                [$cnf($equal(f(f(a2, f(a1, a1)), f(a2, f(a1, a1))),
% 2.93/4.01                        f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))],
% 2.93/4.01                [refute_0_42, refute_0_53])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_55, plain, (d(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(resolve, [$cnf(d(f(f(a2, f(a1, a1)), f(a2, f(a1, a1)))))],
% 2.93/4.01                [refute_0_52, refute_0_54])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_56, plain, (~ c(f(a2, f(a1, f(a1, f(a2, f(a1, a1))))))),
% 2.93/4.01      inference(resolve, [$cnf(d(f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))],
% 2.93/4.01                [refute_0_55, refute_0_46])).
% 2.93/4.01  
% 2.93/4.01  cnf(refute_0_57, plain, ($false),
% 2.93/4.01      inference(resolve, [$cnf(c(f(a2, f(a1, f(a1, f(a2, f(a1, a1)))))))],
% 2.93/4.01                [refute_0_45, refute_0_56])).
% 2.93/4.01  SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/4.01  
%------------------------------------------------------------------------------
