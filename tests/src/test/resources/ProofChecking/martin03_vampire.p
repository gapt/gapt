% Refutation found. Thanks to Tanya!
% SZS status Unsatisfiable for martin03
% SZS output start Proof for martin03
fof(f1,axiom,(
  ! [X0,X1] : ? [X2] : (p(X0,X2,X1) & ~p(X0,X2,X1))),
  file('Problems/martin03.p',a)).
fof(f2,plain,(
  ! [X0,X1] : (p(X0,sK0(X0,X1),X1) & ~p(X0,sK0(X0,X1),X1))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X2,sK0(X0,X1))],[f1])).
fof(f3,plain,(
  ( ! [X0,X1] : (~p(X0,sK0(X0,X1),X1)) )),
  inference(cnf_transformation,[status(thm)],[f2])).
fof(f4,plain,(
  ( ! [X0,X1] : (p(X0,sK0(X0,X1),X1)) )),
  inference(cnf_transformation,[status(thm)],[f2])).
fof(f5,plain,(
  $false),
  inference(forward_subsumption_resolution,[status(thm)],[f4,f3])).
% SZS output end Proof for martin03
% ------------------------------
% Version: Vampire 5.0.1 (Release build, commit 3f1362b99 on 2026-07-01 15:21:00 +0200)
% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 z3-4.8.4-9178-g3c47fd96c
% CaDiCaL version: 2.1.3
% Termination reason: Refutation
% Time elapsed: 0.010 s
% Peak memory usage: 12 MB
% ------------------------------
% ------------------------------
