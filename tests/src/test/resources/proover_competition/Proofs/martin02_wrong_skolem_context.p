% modified vampire proof (expand skolemization steps with f6a), bad bc. sK0 has only one parameter
% Refutation found. Thanks to Tanya!
% SZS status Theorem for martin02
% SZS output start Proof for martin02
fof(f1,axiom,(
  ! [X0,X1] : ? [X2] : (p(X0) & q(X0,X2,X1))),
  file('Problems/martin02.p',a)).
fof(f2,conjecture,(
  ! [X0,X1] : ? [X2] : (p(X0) | q(X0,X2,X1))),
  file('Problems/martin02.p',c)).
fof(f3,negated_conjecture,(
  ~ ! [X0,X1] : ? [X2] : (p(X0) | q(X0,X2,X1))),
  inference(negated_conjecture,[status(cth)],[f2])).
fof(f4,plain,(
  ? [X0,X1] : ! [X2] : (~p(X0) & ~q(X0,X2,X1))),
  inference(ennf_transformation,[status(thm)],[f3])).
fof(f5,plain,(
  ! [X0,X1] : (p(X0) & q(X0,sK0(X0),X1))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK0]),skolemize(X2,sK0(X0))],[f1])).
fof(f6,plain,(
  ! [X2] : (~p(sK1) & ~q(sK1,X2,sK2))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK2]),skolemize(X1,sK2)],[f6a])).
fof(f6a,plain,(
  ?[X1] : ! [X2] : (~p(sK1) & ~q(sK1,X2,X1))),
  inference(skolemize,[status(esa),new_symbols(skolem,[sK1]),skolemize(X0,sK1)],[f4])).
fof(f8,plain,(
  ( ! [X0] : (p(X0)) )),
  inference(cnf_transformation,[status(thm)],[f5])).
fof(f10,plain,(
  ~p(sK1)),
  inference(cnf_transformation,[status(thm)],[f6])).
fof(f11,plain,(
  $false),
  inference(resolution,[status(thm)],[f8,f10])).
% SZS output end Proof for martin02
% ------------------------------
% Version: Vampire 5.0.1 (Release build, commit 3f1362b99 on 2026-07-01 15:21:00 +0200)
% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 z3-4.8.4-9178-g3c47fd96c
% CaDiCaL version: 2.1.3
% Termination reason: Refutation
% Time elapsed: 0.011 s
% Peak memory usage: 15 MB
% Instructions burned: 1 (million)
% ------------------------------
% ------------------------------
