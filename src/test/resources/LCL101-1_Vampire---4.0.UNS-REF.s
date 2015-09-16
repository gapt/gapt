%------------------------------------------------------------------------------
% File       : Vampire---4.0
% Problem    : LCL101-1 : TPTP v6.2.0. Released v1.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n163.star.cs.uiowa.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2609 0 2.40GHz
% Memory     : 32286.75MB
% OS         : Linux 2.6.32-504.23.4.el6.x86_64
% CPULimit   : 300s
% DateTime   : Wed Jul  8 11:54:34 EDT 2015

% Result     : Unsatisfiable 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   19 ( 111 expanded)
%              Number of leaves         :    4 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :   26 ( 192 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Vampire---4.0 format not known, defaulting to TPTP
fof(f1538,plain,(
    $false ),
    inference(resolution,[],[f1227,f4])).

fof(f4,axiom,(
    ~ is_a_theorem(equivalent(equivalent(equivalent(a,b),c),equivalent(equivalent(e,b),equivalent(equivalent(a,e),c)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',prove_p_1)).

fof(f1227,plain,(
    ! [X6,X4,X7,X5] : is_a_theorem(equivalent(equivalent(equivalent(X4,X5),X6),equivalent(equivalent(X7,X5),equivalent(equivalent(X4,X7),X6)))) ),
    inference(resolution,[],[f100,f62])).

fof(f62,plain,(
    ! [X30,X31,X29,X32] : is_a_theorem(equivalent(equivalent(equivalent(equivalent(X29,X30),equivalent(X29,X31)),X32),equivalent(equivalent(X30,X31),X32))) ),
    inference(resolution,[],[f45,f3])).

fof(f3,axiom,(
    ! [X2,X0,X3,X1] : is_a_theorem(equivalent(X0,equivalent(equivalent(equivalent(equivalent(X1,X2),equivalent(X1,X3)),equivalent(X2,X3)),X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',p_4)).

fof(f45,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ is_a_theorem(equivalent(X12,equivalent(equivalent(X15,X13),equivalent(X15,X14))))
      | is_a_theorem(equivalent(X12,equivalent(X13,X14))) ) ),
    inference(resolution,[],[f32,f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ is_a_theorem(equivalent(X0,X1))
      | is_a_theorem(X1)
      | ~ is_a_theorem(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',condensed_detachment)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : is_a_theorem(equivalent(equivalent(X0,equivalent(equivalent(X1,X2),equivalent(X1,X3))),equivalent(X0,equivalent(X2,X3)))) ),
    inference(resolution,[],[f29,f5])).

fof(f5,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ is_a_theorem(equivalent(equivalent(equivalent(equivalent(X1,X2),equivalent(X1,X3)),equivalent(X2,X3)),X0))
      | is_a_theorem(X0) ) ),
    inference(resolution,[],[f2,f1])).

fof(f2,axiom,(
    ! [X2,X0,X3,X1] : is_a_theorem(equivalent(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),X3),X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',lg_2)).

fof(f29,plain,(
    ! [X2,X3,X1] : is_a_theorem(equivalent(equivalent(X1,X2),equivalent(equivalent(X3,X1),equivalent(X3,X2)))) ),
    inference(resolution,[],[f27,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ is_a_theorem(equivalent(equivalent(X2,X0),equivalent(X2,X1)))
      | is_a_theorem(equivalent(X0,X1)) ) ),
    inference(resolution,[],[f10,f1])).

fof(f10,plain,(
    ! [X2,X0,X1] : is_a_theorem(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2))) ),
    inference(resolution,[],[f7,f5])).

fof(f7,plain,(
    ! [X4,X2,X0,X5,X3,X1] : is_a_theorem(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),equivalent(equivalent(equivalent(X3,X4),equivalent(X3,X5)),equivalent(X4,X5)))) ),
    inference(resolution,[],[f5,f3])).

fof(f27,plain,(
    ! [X6,X8,X7,X5] : is_a_theorem(equivalent(equivalent(equivalent(equivalent(X5,X6),equivalent(X5,X7)),equivalent(X6,X7)),equivalent(X8,X8))) ),
    inference(resolution,[],[f21,f6])).

fof(f6,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ is_a_theorem(X3)
      | is_a_theorem(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),X3)) ) ),
    inference(resolution,[],[f3,f1])).

fof(f21,plain,(
    ! [X3] : is_a_theorem(equivalent(X3,X3)) ),
    inference(resolution,[],[f17,f15])).

fof(f17,plain,(
    ! [X0,X1] : is_a_theorem(equivalent(equivalent(X0,X1),equivalent(X0,X1))) ),
    inference(resolution,[],[f15,f7])).

fof(f100,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ is_a_theorem(equivalent(equivalent(equivalent(X19,X16),equivalent(X19,X17)),X18))
      | is_a_theorem(equivalent(equivalent(X16,X17),X18)) ) ),
    inference(resolution,[],[f62,f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.03  % Problem    : LCL101-1 : TPTP v6.2.0. Released v1.0.0.
% 0.00/0.03  % Command    : vampire --mode casc -t %d %s
% 0.02/1.07  % Computer   : n163.star.cs.uiowa.edu
% 0.02/1.07  % Model      : x86_64 x86_64
% 0.02/1.07  % CPU        : Intel(R) Xeon(R) CPU E5-2609 0 @ 2.40GHz
% 0.02/1.07  % Memory     : 32286.75MB
% 0.02/1.07  % OS         : Linux 2.6.32-504.23.4.el6.x86_64
% 0.02/1.07  % CPULimit   : 300
% 0.02/1.07  % DateTime   : Tue Jul  7 10:12:17 CDT 2015
% 0.02/1.07  % CPUTime    : 
% 0.02/1.07  Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!
% 0.02/1.07  % remaining time: 3000 next slice time: 14
% 0.02/1.08  lrs+11_10_bs=unit_only:br=off:gs=on:gsssp=full:nwc=1:stl=30:sos=all:sac=on:sdd=large:ssfp=100000:ssfq=1.2:smm=off:ssnc=none:sp=occurrence:urr=on_13 on theBenchmark
% 1.46/2.58  % (22702)Time limit reached!
% 1.46/2.58  % ------------------------------
% 1.46/2.58  % Version: Vampire 4.0 (commit 2df2fce on 2015-07-07 02:33:56 +0100)
% 1.46/2.58  % Termination reason: Time limit
% 1.46/2.58  % Termination phase: Saturation
% 1.46/2.58  
% 1.46/2.58  % Active clauses: 3419
% 1.46/2.58  % Passive clauses: 10246
% 1.46/2.58  % Generated clauses: 11438
% 1.46/2.58  % Final active clauses: 3419
% 1.46/2.58  % Final passive clauses: 6830
% 1.46/2.58  % Input clauses: 4
% 1.46/2.58  % Initial clauses: 4
% 1.46/2.58  % 
% 1.46/2.58  % Forward subsumptions: 1192
% 1.46/2.58  % 
% 1.46/2.58  % Unit resulting resolution: 11437
% 1.46/2.58  % 
% 1.46/2.58  % SAT solver clauses: 10246
% 1.46/2.58  % SAT solver unit clauses: 10246
% 1.46/2.58  % 
% 1.46/2.58  % TWLsolver clauses: 10246
% 1.46/2.58  % TWLsolver calls for satisfiability: 10246
% 1.46/2.58  % 
% 1.46/2.58  % Memory used [KB]: 34029
% 1.46/2.58  % Time elapsed: 1.500 s
% 1.46/2.58  % ------------------------------
% 1.46/2.58  ----  Runtime statistics ----
% 1.46/2.58  clauses created: 11441
% 1.46/2.58  clauses deleted: 1192
% 1.46/2.58  -----------------------------
% 1.46/2.58  % ------------------------------
% 1.46/2.58  % remaining time: 2984 next slice time: 3
% 1.46/2.58  dis+1002_5_gs=on:gsem=off:gsssp=full:lwlo=on:nwc=1:sas=minisat:sos=on:sac=on:sdd=large:sfr=on:ssfp=100000:ssfq=1.0:ssnc=none:sp=reverse_arity_1 on theBenchmark
% 1.46/2.58  % Refutation not found, incomplete strategy
% 1.46/2.58  % ------------------------------
% 1.46/2.58  % Version: Vampire 4.0 (commit 2df2fce on 2015-07-07 02:33:56 +0100)
% 1.46/2.58  % Termination reason: Refutation not found, incomplete strategy
% 1.46/2.58  
% 1.46/2.58  % Active clauses: 4
% 1.46/2.58  % Passive clauses: 1
% 1.46/2.58  % Generated clauses: 1
% 1.46/2.58  % Final active clauses: 4
% 1.46/2.58  % Input clauses: 4
% 1.46/2.58  % Initial clauses: 4
% 1.46/2.58  % 
% 1.46/2.58  % SAT solver clauses: 4
% 1.46/2.58  % SAT solver unit clauses: 2
% 1.46/2.58  % 
% 1.46/2.58  % Memory used [KB]: 511
% 1.46/2.58  % Time elapsed: 0.002 s
% 1.46/2.58  % ------------------------------
% 1.46/2.58  ----  Runtime statistics ----
% 1.46/2.58  clauses created: 4
% 1.46/2.58  -----------------------------
% 1.46/2.58  % ------------------------------
% 1.46/2.58  % remaining time: 2984 next slice time: 123
% 1.46/2.59  dis+1_40_bs=unit_only:fsr=off:nwc=1:sas=minisat:sdd=large:ssfp=1000:ssfq=1.1:smm=sco:ssnc=none:sp=reverse_arity:updr=off_117 on theBenchmark
% 1.54/2.60  % Refutation found. Thanks to Tanya!
% 1.54/2.60  % SZS status Unsatisfiable for theBenchmark
% 1.54/2.60  % SZS output start Proof for theBenchmark
% 1.54/2.60  fof(f1538,plain,(
% 1.54/2.60    $false),
% 1.54/2.60    inference(resolution,[],[f1227,f4])).
% 1.54/2.60  fof(f4,axiom,(
% 1.54/2.60    ~is_a_theorem(equivalent(equivalent(equivalent(a,b),c),equivalent(equivalent(e,b),equivalent(equivalent(a,e),c))))),
% 1.54/2.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',prove_p_1)).
% 1.54/2.60  fof(f1227,plain,(
% 1.54/2.60    ( ! [X6,X4,X7,X5] : (is_a_theorem(equivalent(equivalent(equivalent(X4,X5),X6),equivalent(equivalent(X7,X5),equivalent(equivalent(X4,X7),X6))))) )),
% 1.54/2.60    inference(resolution,[],[f100,f62])).
% 1.54/2.60  fof(f62,plain,(
% 1.54/2.60    ( ! [X30,X31,X29,X32] : (is_a_theorem(equivalent(equivalent(equivalent(equivalent(X29,X30),equivalent(X29,X31)),X32),equivalent(equivalent(X30,X31),X32)))) )),
% 1.54/2.60    inference(resolution,[],[f45,f3])).
% 1.54/2.60  fof(f3,axiom,(
% 1.54/2.60    ( ! [X2,X0,X3,X1] : (is_a_theorem(equivalent(X0,equivalent(equivalent(equivalent(equivalent(X1,X2),equivalent(X1,X3)),equivalent(X2,X3)),X0)))) )),
% 1.54/2.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',p_4)).
% 1.54/2.60  fof(f45,plain,(
% 1.54/2.60    ( ! [X14,X12,X15,X13] : (~is_a_theorem(equivalent(X12,equivalent(equivalent(X15,X13),equivalent(X15,X14)))) | is_a_theorem(equivalent(X12,equivalent(X13,X14)))) )),
% 1.54/2.60    inference(resolution,[],[f32,f1])).
% 1.54/2.60  fof(f1,axiom,(
% 1.54/2.60    ( ! [X0,X1] : (~is_a_theorem(equivalent(X0,X1)) | is_a_theorem(X1) | ~is_a_theorem(X0)) )),
% 1.54/2.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',condensed_detachment)).
% 1.54/2.60  fof(f32,plain,(
% 1.54/2.60    ( ! [X2,X0,X3,X1] : (is_a_theorem(equivalent(equivalent(X0,equivalent(equivalent(X1,X2),equivalent(X1,X3))),equivalent(X0,equivalent(X2,X3))))) )),
% 1.54/2.60    inference(resolution,[],[f29,f5])).
% 1.54/2.60  fof(f5,plain,(
% 1.54/2.60    ( ! [X2,X0,X3,X1] : (~is_a_theorem(equivalent(equivalent(equivalent(equivalent(X1,X2),equivalent(X1,X3)),equivalent(X2,X3)),X0)) | is_a_theorem(X0)) )),
% 1.54/2.60    inference(resolution,[],[f2,f1])).
% 1.54/2.60  fof(f2,axiom,(
% 1.54/2.60    ( ! [X2,X0,X3,X1] : (is_a_theorem(equivalent(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),X3),X3))) )),
% 1.54/2.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',lg_2)).
% 1.54/2.60  fof(f29,plain,(
% 1.54/2.60    ( ! [X2,X3,X1] : (is_a_theorem(equivalent(equivalent(X1,X2),equivalent(equivalent(X3,X1),equivalent(X3,X2))))) )),
% 1.54/2.60    inference(resolution,[],[f27,f15])).
% 1.54/2.60  fof(f15,plain,(
% 1.54/2.60    ( ! [X2,X0,X1] : (~is_a_theorem(equivalent(equivalent(X2,X0),equivalent(X2,X1))) | is_a_theorem(equivalent(X0,X1))) )),
% 1.54/2.60    inference(resolution,[],[f10,f1])).
% 1.54/2.60  fof(f10,plain,(
% 1.54/2.60    ( ! [X2,X0,X1] : (is_a_theorem(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)))) )),
% 1.54/2.60    inference(resolution,[],[f7,f5])).
% 1.54/2.60  fof(f7,plain,(
% 1.54/2.60    ( ! [X4,X2,X0,X5,X3,X1] : (is_a_theorem(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),equivalent(equivalent(equivalent(X3,X4),equivalent(X3,X5)),equivalent(X4,X5))))) )),
% 1.54/2.60    inference(resolution,[],[f5,f3])).
% 1.54/2.60  fof(f27,plain,(
% 1.54/2.60    ( ! [X6,X8,X7,X5] : (is_a_theorem(equivalent(equivalent(equivalent(equivalent(X5,X6),equivalent(X5,X7)),equivalent(X6,X7)),equivalent(X8,X8)))) )),
% 1.54/2.60    inference(resolution,[],[f21,f6])).
% 1.54/2.60  fof(f6,plain,(
% 1.54/2.60    ( ! [X2,X0,X3,X1] : (~is_a_theorem(X3) | is_a_theorem(equivalent(equivalent(equivalent(equivalent(X0,X1),equivalent(X0,X2)),equivalent(X1,X2)),X3))) )),
% 1.54/2.60    inference(resolution,[],[f3,f1])).
% 1.54/2.60  fof(f21,plain,(
% 1.54/2.60    ( ! [X3] : (is_a_theorem(equivalent(X3,X3))) )),
% 1.54/2.60    inference(resolution,[],[f17,f15])).
% 1.54/2.60  fof(f17,plain,(
% 1.54/2.60    ( ! [X0,X1] : (is_a_theorem(equivalent(equivalent(X0,X1),equivalent(X0,X1)))) )),
% 1.54/2.60    inference(resolution,[],[f15,f7])).
% 1.54/2.60  fof(f100,plain,(
% 1.54/2.60    ( ! [X19,X17,X18,X16] : (~is_a_theorem(equivalent(equivalent(equivalent(X19,X16),equivalent(X19,X17)),X18)) | is_a_theorem(equivalent(equivalent(X16,X17),X18))) )),
% 1.54/2.60    inference(resolution,[],[f62,f1])).
% 1.54/2.60  % SZS output end Proof for theBenchmark
% 1.54/2.60  % ------------------------------
% 1.54/2.60  % Version: Vampire 4.0 (commit 2df2fce on 2015-07-07 02:33:56 +0100)
% 1.54/2.60  % Termination reason: Refutation
% 1.54/2.60  
% 1.54/2.60  % Active clauses: 90
% 1.54/2.60  % Passive clauses: 893
% 1.54/2.60  % Generated clauses: 1566
% 1.54/2.60  % Final active clauses: 88
% 1.54/2.60  % Final passive clauses: 781
% 1.54/2.60  % Input clauses: 4
% 1.54/2.60  % Initial clauses: 4
% 1.54/2.60  % 
% 1.54/2.60  % Simple tautologies: 2
% 1.54/2.60  % Forward subsumptions: 656
% 1.54/2.60  % Backward subsumptions: 1
% 1.54/2.60  % 
% 1.54/2.60  % Binary resolution: 1560
% 1.54/2.60  % 
% 1.54/2.60  % Split clauses: 1
% 1.54/2.60  % Split components: 2
% 1.54/2.60  % SAT solver clauses: 9
% 1.54/2.60  % SAT solver unit clauses: 7
% 1.54/2.60  % SAT solver binary clauses: 1
% 1.54/2.60  % 
% 1.54/2.60  % Sat splits: 1
% 1.54/2.60  % Sat splitting refutations: 7
% 1.54/2.60  % 
% 1.54/2.60  % Memory used [KB]: 1407
% 1.54/2.60  % Time elapsed: 0.017 s
% 1.54/2.60  % ------------------------------
% 1.54/2.60  ----  Runtime statistics ----
% 1.54/2.60  clauses created: 1566
% 1.54/2.60  clauses deleted: 664
% 1.54/2.60  ssat_new_components: 2
% 1.54/2.60  ssat_sat_clauses: 8
% 1.54/2.60  unworthy child removed: 1
% 1.54/2.60  -----------------------------
% 1.54/2.60  % ------------------------------
% 1.54/2.60  % Success in time 1.532 s
%------------------------------------------------------------------------------
