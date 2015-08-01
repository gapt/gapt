% SZS status Theorem for samples/simple.p
Start of proof for samples/simple.p
%-----------------------------------------------------
fof(goal, conjecture, p(f(f(f(f(f(f(f(f(f(z)))))))))), file('samples/simple.p', goal)).
fof(base_case, axiom, p(z), file('samples/simple.p', base_case)).
fof(induction_step, axiom, ! [_5743] : (p(_5743) => p(f(_5743))), file('samples/simple.p', induction_step)).

cnf(1, plain, [p(f(f(f(f(f(f(f(f(f(z))))))))))], clausify(goal)).
cnf(2, plain, [-(p(z))], clausify(base_case)).
cnf(3, plain, [p(_2427), -(p(f(_2427)))], clausify(induction_step)).

cnf('1',plain,[p(f(f(f(f(f(f(f(f(f(z))))))))))],start(1)).
cnf('1.1',plain,[-(p(f(f(f(f(f(f(f(f(f(z))))))))))), p(f(f(f(f(f(f(f(f(z)))))))))],extension(3,bind([[_2427], [f(f(f(f(f(f(f(f(z))))))))]]))).
cnf('1.1.1',plain,[-(p(f(f(f(f(f(f(f(f(z)))))))))), p(f(f(f(f(f(f(f(z))))))))],extension(3,bind([[_2427], [f(f(f(f(f(f(f(z)))))))]]))).
cnf('1.1.1.1',plain,[-(p(f(f(f(f(f(f(f(z))))))))), p(f(f(f(f(f(f(z)))))))],extension(3,bind([[_2427], [f(f(f(f(f(f(z))))))]]))).
cnf('1.1.1.1.1',plain,[-(p(f(f(f(f(f(f(z)))))))), p(f(f(f(f(f(z))))))],extension(3,bind([[_2427], [f(f(f(f(f(z)))))]]))).
cnf('1.1.1.1.1.1',plain,[-(p(f(f(f(f(f(z))))))), p(f(f(f(f(z)))))],extension(3,bind([[_2427], [f(f(f(f(z))))]]))).
cnf('1.1.1.1.1.1.1',plain,[-(p(f(f(f(f(z)))))), p(f(f(f(z))))],extension(3,bind([[_2427], [f(f(f(z)))]]))).
cnf('1.1.1.1.1.1.1.1',plain,[-(p(f(f(f(z))))), p(f(f(z)))],extension(3,bind([[_2427], [f(f(z))]]))).
cnf('1.1.1.1.1.1.1.1.1',plain,[-(p(f(f(z)))), p(f(z))],extension(3,bind([[_2427], [f(z)]]))).
cnf('1.1.1.1.1.1.1.1.1.1',plain,[-(p(f(z))), p(z)],extension(3,bind([[_2427], [z]]))).
cnf('1.1.1.1.1.1.1.1.1.1.1',plain,[-(p(z))],extension(2)).
%-----------------------------------------------------
End of proof for samples/simple.p
