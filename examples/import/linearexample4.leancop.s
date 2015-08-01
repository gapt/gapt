% SZS status Theorem for samples/simple.p
%Start of proof for samples/simple.p
%-----------------------------------------------------
fof(goal, conjecture, p(f(f(f(f(z))))), file('samples/simple.p', goal)).
fof(base_case, axiom, p(z), file('samples/simple.p', base_case)).
fof(induction_step, axiom, ! [_4311] : (p(_4311) => p(f(_4311))), file('samples/simple.p', induction_step)).
%
cnf(1, plain, [p(f(f(f(f(z)))))], clausify(goal)).
cnf(2, plain, [-(p(z))], clausify(base_case)).
cnf(3, plain, [p(_2407), -(p(f(_2407)))], clausify(induction_step)).
%
cnf('1',plain,[p(f(f(f(f(z)))))],start(1)).
cnf('1.1',plain,[-(p(f(f(f(f(z)))))), p(f(f(f(z))))],extension(3,bind([[_2407], [f(f(f(z)))]]))).
cnf('1.1.1',plain,[-(p(f(f(f(z))))), p(f(f(z)))],extension(3,bind([[_2407], [f(f(z))]]))).
cnf('1.1.1.1',plain,[-(p(f(f(z)))), p(f(z))],extension(3,bind([[_2407], [f(z)]]))).
cnf('1.1.1.1.1',plain,[-(p(f(z))), p(z)],extension(3,bind([[_2407], [z]]))).
cnf('1.1.1.1.1.1',plain,[-(p(z))],extension(2)).
%-----------------------------------------------------
%End of proof for samples/simple.p
