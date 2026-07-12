% Refutation found. Thanks to Tanya!
% SZS status Theorem for linear_example_26
% SZS output start Proof for linear_example_26
fof(f1,axiom,(
  ! [X0] : ('P'(X0) => 'P'(s(X0)))),
  file('../../ProoVer_competition/Proofs/Problems/linear_example_26.p',a0)).
fof(f2,axiom,(
  'P'('0')),
  file('../../ProoVer_competition/Proofs/Problems/linear_example_26.p',a1)).
fof(f3,conjecture,(
  'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))))),
  file('../../ProoVer_competition/Proofs/Problems/linear_example_26.p',c)).
fof(f4,negated_conjecture,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))))),
  inference(negated_conjecture,[status(cth)],[f3])).
fof(f5,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))))),
  inference(flattening,[status(thm)],[f4])).
fof(f6,plain,(
  ! [X0] : ('P'(s(X0)) | ~'P'(X0))),
  inference(ennf_transformation,[status(thm)],[f1])).
fof(f7,plain,(
  ( ! [X0] : ('P'(s(X0)) | ~'P'(X0)) )),
  inference(cnf_transformation,[status(thm)],[f6])).
fof(f8,plain,(
  'P'('0')),
  inference(cnf_transformation,[status(thm)],[f2])).
fof(f9,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))))),
  inference(cnf_transformation,[status(thm)],[f5])).
fof(f10,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))),
  inference(resolution,[status(thm)],[f7,f9])).
fof(f11,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))),
  inference(resolution,[status(thm)],[f10,f7])).
fof(f12,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))),
  inference(resolution,[status(thm)],[f11,f7])).
fof(f13,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))),
  inference(resolution,[status(thm)],[f12,f7])).
fof(f14,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))),
  inference(resolution,[status(thm)],[f13,f7])).
fof(f15,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))),
  inference(resolution,[status(thm)],[f14,f7])).
fof(f16,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))),
  inference(resolution,[status(thm)],[f15,f7])).
fof(f17,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))),
  inference(resolution,[status(thm)],[f16,f7])).
fof(f18,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))),
  inference(resolution,[status(thm)],[f17,f7])).
fof(f19,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))),
  inference(resolution,[status(thm)],[f18,f7])).
fof(f20,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))),
  inference(resolution,[status(thm)],[f19,f7])).
fof(f21,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))),
  inference(resolution,[status(thm)],[f20,f7])).
fof(f22,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))),
  inference(resolution,[status(thm)],[f21,f7])).
fof(f23,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))),
  inference(resolution,[status(thm)],[f22,f7])).
fof(f24,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))),
  inference(resolution,[status(thm)],[f23,f7])).
fof(f25,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s(s('0')))))))))))),
  inference(resolution,[status(thm)],[f24,f7])).
fof(f26,plain,(
  ~'P'(s(s(s(s(s(s(s(s(s('0'))))))))))),
  inference(resolution,[status(thm)],[f25,f7])).
fof(f27,plain,(
  ~'P'(s(s(s(s(s(s(s(s('0')))))))))),
  inference(resolution,[status(thm)],[f26,f7])).
fof(f28,plain,(
  ~'P'(s(s(s(s(s(s(s('0'))))))))),
  inference(resolution,[status(thm)],[f27,f7])).
fof(f29,plain,(
  ~'P'(s(s(s(s(s(s('0')))))))),
  inference(resolution,[status(thm)],[f28,f7])).
fof(f30,plain,(
  ~'P'(s(s(s(s(s('0'))))))),
  inference(resolution,[status(thm)],[f29,f7])).
fof(f31,plain,(
  ~'P'(s(s(s(s('0')))))),
  inference(resolution,[status(thm)],[f30,f7])).
fof(f32,plain,(
  ~'P'(s(s(s('0'))))),
  inference(resolution,[status(thm)],[f31,f7])).
fof(f33,plain,(
  ~'P'(s(s('0')))),
  inference(resolution,[status(thm)],[f32,f7])).
fof(f34,plain,(
  ~'P'(s('0'))),
  inference(resolution,[status(thm)],[f33,f7])).
fof(f35,plain,(
  ~'P'('0')),
  inference(resolution,[status(thm)],[f34,f7])).
fof(f36,plain,(
  $false),
  inference(forward_subsumption_resolution,[status(thm)],[f35,f8])).
% SZS output end Proof for linear_example_26
% ------------------------------
% Version: Vampire 5.0.1 (Release build, commit 3f1362b99 on 2026-07-01 15:21:00 +0200)
% Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 z3-4.8.4-9178-g3c47fd96c
% CaDiCaL version: 2.1.3
% Termination reason: Refutation
% Time elapsed: 0.011 s
% Peak memory usage: 12 MB
% Instructions burned: 3 (million)
% ------------------------------
% ------------------------------
