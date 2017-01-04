%------------------------------------------------------------------------------
% File       : VampireZ3---1.0
% Problem    : SYN728-1 : TPTP v6.2.0. Released v2.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampireZ3 --mode casc -m 20000 -t %d %s

% Computer   : n038.star.cs.uiowa.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2609 0 2.40GHz
% Memory     : 32286.75MB
% OS         : Linux 2.6.32-573.1.1.el6.x86_64
% CPULimit   : 300s
% DateTime   : Fri Sep 18 20:51:35 EDT 2015

% Result     : Unsatisfiable 0.04s
% Output     : Refutation 0.04s
% Verified   : 
% Statistics : Number of formulae       :   34 (  66 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :    3
%              Number of atoms          :   87 ( 163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: VampireZ3---1.0 format not known, defaulting to TPTP
fof(f25,plain,(
    $false ),
    inference(sat_splitting_refutation,[],[f4,f6,f2,f7,f1,f9,f8,f5,f12,f10,f3,f13,f14,f15,f16,f17,f18,f20,f21,f19,f22,f24,f23])).

fof(f23,plain,
    ( $false
    | $spl8
    | $spl18 ),
    inference(resolution,[],[f10,f19])).

fof(f24,plain,
    ( $false
    | $spl4
    | $spl8 ),
    inference(resolution,[],[f10,f8])).

fof(f22,plain,
    ( $false
    | $spl6
    | $spl18 ),
    inference(resolution,[],[f19,f9])).

fof(f19,plain,
    ( ! [X0] : p(X0,sk1(X0))
    | $spl18 ),
    inference(cnf_transformation,[],[f19_D])).

fof(f19_D,plain,
    ( ! [X0] : p(X0,sk1(X0))
  <=> ~ $spl18 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl18])])).

fof(f21,plain,
    ( ! [X0] : p(X0,sk1(X0))
    | $spl6
    | $spl16 ),
    inference(resolution,[],[f9,f17])).

fof(f20,plain,
    ( $false
    | $spl4
    | $spl11 ),
    inference(resolution,[],[f12,f8])).

fof(f18,plain,
    ( ! [X0] : p(X0,sk1(X0))
    | $spl6
    | $spl16 ),
    inference(resolution,[],[f17,f9])).

fof(f17,plain,
    ( ! [X0] :
        ( p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0)))))
        | p(X0,sk1(X0)) )
    | $spl16 ),
    inference(cnf_transformation,[],[f17_D])).

fof(f17_D,plain,
    ( ! [X0] :
        ( p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0)))))
        | p(X0,sk1(X0)) )
  <=> ~ $spl16 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl16])])).

fof(f16,plain,
    ( ! [X0] :
        ( p(X0,sk1(X0))
        | p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0))))) )
    | $spl12
    | $spl14 ),
    inference(resolution,[],[f13,f15])).

fof(f15,plain,
    ( ! [X0] :
        ( ~ q(X0)
        | p(g(X0),sk1(g(X0))) )
    | $spl14 ),
    inference(cnf_transformation,[],[f15_D])).

fof(f15_D,plain,
    ( ! [X0] :
        ( ~ q(X0)
        | p(g(X0),sk1(g(X0))) )
  <=> ~ $spl14 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl14])])).

fof(f14,plain,
    ( ! [X0] :
        ( p(g(X0),sk1(g(X0)))
        | ~ q(X0) )
    | $spl0
    | $spl2 ),
    inference(resolution,[],[f7,f6])).

fof(f13,plain,
    ( ! [X1] :
        ( q(f(X1,sk1(X1)))
        | p(X1,sk1(X1)) )
    | $spl12 ),
    inference(cnf_transformation,[],[f13_D])).

fof(f13_D,plain,
    ( ! [X1] :
        ( q(f(X1,sk1(X1)))
        | p(X1,sk1(X1)) )
  <=> ~ $spl12 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl12])])).

fof(f3,axiom,(
    ! [X1] :
      ( p(X1,sk1(X1))
      | q(f(X1,sk1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_3)).

fof(f10,plain,
    ( ! [X1] : ~ p(g(sk2),X1)
    | $spl8 ),
    inference(cnf_transformation,[],[f10_D])).

fof(f10_D,plain,
    ( ! [X1] : ~ p(g(sk2),X1)
  <=> ~ $spl8 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl8])])).

fof(f12,plain,
    ( ~ p(sk2,sk2)
    | $spl11 ),
    inference(cnf_transformation,[],[f12_D])).

fof(f12_D,plain,
    ( ~ p(sk2,sk2)
  <=> ~ $spl11 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl11])])).

fof(f5,axiom,(
    ! [X1] :
      ( ~ p(sk2,sk2)
      | ~ p(g(sk2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_5)).

fof(f8,plain,
    ( ! [X0] : p(X0,X0)
    | $spl4 ),
    inference(cnf_transformation,[],[f8_D])).

fof(f8_D,plain,
    ( ! [X0] : p(X0,X0)
  <=> ~ $spl4 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl4])])).

fof(f9,plain,
    ( ! [X2,X1] : ~ p(X1,X2)
    | $spl6 ),
    inference(cnf_transformation,[],[f9_D])).

fof(f9_D,plain,
    ( ! [X2,X1] : ~ p(X1,X2)
  <=> ~ $spl6 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl6])])).

fof(f1,axiom,(
    ! [X2,X0,X1] :
      ( ~ p(X1,X2)
      | p(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_1)).

fof(f7,plain,
    ( ! [X1] :
        ( m(X1)
        | p(X1,sk1(X1)) )
    | $spl2 ),
    inference(cnf_transformation,[],[f7_D])).

fof(f7_D,plain,
    ( ! [X1] :
        ( m(X1)
        | p(X1,sk1(X1)) )
  <=> ~ $spl2 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl2])])).

fof(f2,axiom,(
    ! [X1] :
      ( m(X1)
      | p(X1,sk1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_2)).

fof(f6,plain,
    ( ! [X1] :
        ( ~ m(g(X1))
        | ~ q(X1) )
    | $spl0 ),
    inference(cnf_transformation,[],[f6_D])).

fof(f6_D,plain,
    ( ! [X1] :
        ( ~ m(g(X1))
        | ~ q(X1) )
  <=> ~ $spl0 ),
    introduced(sat_splitting_component,[new_symbols(naming,[$spl0])])).

fof(f4,axiom,(
    ! [X1] :
      ( ~ q(X1)
      | ~ m(g(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_4)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.02  % Problem    : SYN728-1 : TPTP v6.2.0. Released v2.5.0.
% 0.01/0.03  % Command    : vampireZ3 --mode casc -m 20000 -t %d %s
% 0.01/1.06  % Computer   : n038.star.cs.uiowa.edu
% 0.01/1.06  % Model      : x86_64 x86_64
% 0.01/1.06  % CPU        : Intel(R) Xeon(R) CPU E5-2609 0 @ 2.40GHz
% 0.01/1.06  % Memory     : 32286.75MB
% 0.01/1.06  % OS         : Linux 2.6.32-573.1.1.el6.x86_64
% 0.01/1.06  % CPULimit   : 300
% 0.01/1.06  % DateTime   : Fri Sep 18 11:40:46 CDT 2015
% 0.01/1.07  % CPUTime    : 
% 0.01/1.07  Hi Geoff, go and have some cold beer while I am trying to solve this very hard problem!
% 0.01/1.07  % remaining time: 3000 next slice time: 3
% 0.01/1.10  dis+1011_5_fsr=off:gs=on:gsaa=full_model:gsssp=full:nwc=1:sas=z3:sos=on:ssfp=40000:ssfq=2.0:smm=sco:ssnc=all:tha=off:updr=off_1 on theBenchmark
% 0.04/1.11  % Refutation found. Thanks to Tanya!
% 0.04/1.11  % SZS status Unsatisfiable for theBenchmark
% 0.04/1.11  % SZS output start Proof for theBenchmark
% 0.04/1.11  fof(f25,plain,(
% 0.04/1.11    $false),
% 0.04/1.11    inference(sat_splitting_refutation,[],[f4,f6,f2,f7,f1,f9,f8,f5,f12,f10,f3,f13,f14,f15,f16,f17,f18,f20,f21,f19,f22,f24,f23])).
% 0.04/1.11  fof(f23,plain,(
% 0.04/1.11    $false | ($spl8 | $spl18)),
% 0.04/1.11    inference(resolution,[],[f10,f19])).
% 0.04/1.11  fof(f24,plain,(
% 0.04/1.11    $false | ($spl4 | $spl8)),
% 0.04/1.11    inference(resolution,[],[f10,f8])).
% 0.04/1.11  fof(f22,plain,(
% 0.04/1.11    $false | ($spl6 | $spl18)),
% 0.04/1.11    inference(resolution,[],[f19,f9])).
% 0.04/1.11  fof(f19,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,sk1(X0))) ) | $spl18),
% 0.04/1.11    inference(cnf_transformation,[],[f19_D])).
% 0.04/1.11  fof(f19_D,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,sk1(X0))) ) <=> ~$spl18),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl18])])).
% 0.04/1.11  fof(f21,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,sk1(X0))) ) | ($spl6 | $spl16)),
% 0.04/1.11    inference(resolution,[],[f9,f17])).
% 0.04/1.11  fof(f20,plain,(
% 0.04/1.11    $false | ($spl4 | $spl11)),
% 0.04/1.11    inference(resolution,[],[f12,f8])).
% 0.04/1.11  fof(f18,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,sk1(X0))) ) | ($spl6 | $spl16)),
% 0.04/1.11    inference(resolution,[],[f17,f9])).
% 0.04/1.11  fof(f17,plain,(
% 0.04/1.11    ( ! [X0] : (p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0))))) | p(X0,sk1(X0))) ) | $spl16),
% 0.04/1.11    inference(cnf_transformation,[],[f17_D])).
% 0.04/1.11  fof(f17_D,plain,(
% 0.04/1.11    ( ! [X0] : (p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0))))) | p(X0,sk1(X0))) ) <=> ~$spl16),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl16])])).
% 0.04/1.11  fof(f16,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,sk1(X0)) | p(g(f(X0,sk1(X0))),sk1(g(f(X0,sk1(X0)))))) ) | ($spl12 | $spl14)),
% 0.04/1.11    inference(resolution,[],[f13,f15])).
% 0.04/1.11  fof(f15,plain,(
% 0.04/1.11    ( ! [X0] : (~q(X0) | p(g(X0),sk1(g(X0)))) ) | $spl14),
% 0.04/1.11    inference(cnf_transformation,[],[f15_D])).
% 0.04/1.11  fof(f15_D,plain,(
% 0.04/1.11    ( ! [X0] : (~q(X0) | p(g(X0),sk1(g(X0)))) ) <=> ~$spl14),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl14])])).
% 0.04/1.11  fof(f14,plain,(
% 0.04/1.11    ( ! [X0] : (p(g(X0),sk1(g(X0))) | ~q(X0)) ) | ($spl0 | $spl2)),
% 0.04/1.11    inference(resolution,[],[f7,f6])).
% 0.04/1.11  fof(f13,plain,(
% 0.04/1.11    ( ! [X1] : (q(f(X1,sk1(X1))) | p(X1,sk1(X1))) ) | $spl12),
% 0.04/1.11    inference(cnf_transformation,[],[f13_D])).
% 0.04/1.11  fof(f13_D,plain,(
% 0.04/1.11    ( ! [X1] : (q(f(X1,sk1(X1))) | p(X1,sk1(X1))) ) <=> ~$spl12),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl12])])).
% 0.04/1.11  fof(f3,axiom,(
% 0.04/1.11    ( ! [X1] : (p(X1,sk1(X1)) | q(f(X1,sk1(X1)))) )),
% 0.04/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_3)).
% 0.04/1.11  fof(f10,plain,(
% 0.04/1.11    ( ! [X1] : (~p(g(sk2),X1)) ) | $spl8),
% 0.04/1.11    inference(cnf_transformation,[],[f10_D])).
% 0.04/1.11  fof(f10_D,plain,(
% 0.04/1.11    ( ! [X1] : (~p(g(sk2),X1)) ) <=> ~$spl8),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl8])])).
% 0.04/1.11  fof(f12,plain,(
% 0.04/1.11    ~p(sk2,sk2) | $spl11),
% 0.04/1.11    inference(cnf_transformation,[],[f12_D])).
% 0.04/1.11  fof(f12_D,plain,(
% 0.04/1.11    ~p(sk2,sk2) <=> ~$spl11),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl11])])).
% 0.04/1.11  fof(f5,axiom,(
% 0.04/1.11    ( ! [X1] : (~p(sk2,sk2) | ~p(g(sk2),X1)) )),
% 0.04/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_5)).
% 0.04/1.11  fof(f8,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,X0)) ) | $spl4),
% 0.04/1.11    inference(cnf_transformation,[],[f8_D])).
% 0.04/1.11  fof(f8_D,plain,(
% 0.04/1.11    ( ! [X0] : (p(X0,X0)) ) <=> ~$spl4),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl4])])).
% 0.04/1.11  fof(f9,plain,(
% 0.04/1.11    ( ! [X2,X1] : (~p(X1,X2)) ) | $spl6),
% 0.04/1.11    inference(cnf_transformation,[],[f9_D])).
% 0.04/1.11  fof(f9_D,plain,(
% 0.04/1.11    ( ! [X2,X1] : (~p(X1,X2)) ) <=> ~$spl6),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl6])])).
% 0.04/1.11  fof(f1,axiom,(
% 0.04/1.11    ( ! [X2,X0,X1] : (~p(X1,X2) | p(X0,X0)) )),
% 0.04/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_1)).
% 0.04/1.11  fof(f7,plain,(
% 0.04/1.11    ( ! [X1] : (m(X1) | p(X1,sk1(X1))) ) | $spl2),
% 0.04/1.11    inference(cnf_transformation,[],[f7_D])).
% 0.04/1.11  fof(f7_D,plain,(
% 0.04/1.11    ( ! [X1] : (m(X1) | p(X1,sk1(X1))) ) <=> ~$spl2),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl2])])).
% 0.04/1.11  fof(f2,axiom,(
% 0.04/1.11    ( ! [X1] : (m(X1) | p(X1,sk1(X1))) )),
% 0.04/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_2)).
% 0.04/1.11  fof(f6,plain,(
% 0.04/1.11    ( ! [X1] : (~m(g(X1)) | ~q(X1)) ) | $spl0),
% 0.04/1.11    inference(cnf_transformation,[],[f6_D])).
% 0.04/1.11  fof(f6_D,plain,(
% 0.04/1.11    ( ! [X1] : (~m(g(X1)) | ~q(X1)) ) <=> ~$spl0),
% 0.04/1.11    introduced(sat_splitting_component,[new_symbols(naming,[$spl0])])).
% 0.04/1.11  fof(f4,axiom,(
% 0.04/1.11    ( ! [X1] : (~q(X1) | ~m(g(X1))) )),
% 0.04/1.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',thm69_4)).
% 0.04/1.11  % SZS output end Proof for theBenchmark
% 0.04/1.11  % ------------------------------
% 0.04/1.11  % Version: Vampire 4.0 (commit 86336e9 on 2015-07-16 10:10:01 +0100)
% 0.04/1.11  % Termination reason: Refutation
% 0.04/1.11  
% 0.04/1.11  % Active clauses: 12
% 0.04/1.11  % Passive clauses: 13
% 0.04/1.11  % Generated clauses: 26
% 0.04/1.11  % Final active clauses: 8
% 0.04/1.11  % Input clauses: 5
% 0.04/1.11  % Initial clauses: 5
% 0.04/1.11  % 
% 0.04/1.11  % Forward subsumptions: 1
% 0.04/1.11  % 
% 0.04/1.11  % Binary resolution: 8
% 0.04/1.11  % 
% 0.04/1.11  % Split clauses: 2
% 0.04/1.11  % Split components: 4
% 0.04/1.11  % SAT solver clauses: 49
% 0.04/1.11  % SAT solver unit clauses: 3
% 0.04/1.11  % SAT solver binary clauses: 26
% 0.04/1.11  % 
% 0.04/1.11  % Sat splits: 2
% 0.04/1.11  % Sat splitting refutations: 4
% 0.04/1.11  % 
% 0.04/1.11  % Memory used [KB]: 511
% 0.04/1.11  % Time elapsed: 0.013 s
% 0.04/1.11  % ------------------------------
% 0.04/1.11  ----  Runtime statistics ----
% 0.04/1.11  clauses created: 25
% 0.04/1.11  clauses deleted: 1
% 0.04/1.11  ssat_new_components: 10
% 0.04/1.11  ssat_non_splittable_introduced_components: 6
% 0.04/1.11  ssat_non_splittable_sat_clauses: 7
% 0.04/1.11  ssat_sat_clauses: 13
% 0.04/1.11  total_frozen: 1
% 0.04/1.11  total_unfrozen: 1
% 0.04/1.11  unworthy child removed: 9
% 0.04/1.11  -----------------------------
% 0.04/1.11  % ------------------------------
% 0.04/1.11  % Success in time 0.045 s
%------------------------------------------------------------------------------
