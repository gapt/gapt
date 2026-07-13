fof(a0, axiom, ![X]: ('P'(X) => 'P'(s(X))), file('Problems/linear_example_15.p', a0)).
fof(a1, axiom, 'P'('0'), file('Problems/linear_example_15.p', a1)).
fof(c, conjecture, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), file('Problems/linear_example_15.p', c)).
fof(nc, negated_conjecture, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(negated_conjecture, [status(cth)], [c])).
fof(p0, plain, 'P'('0') => 'P'('0'), inference(logical_axiom, [status(thm)], [])).
fof(p1, plain, 'P'(s('0')) => 'P'(s('0')), inference(logical_axiom, [status(thm)], [])).
fof(p2, plain, (('P'('0') => 'P'(s('0'))) & 'P'('0')) => 'P'(s('0')), inference(imp_left, [status(thm)], [p0, p1])).
fof(p3, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s('0')), inference(forall_left, [status(thm)], [p2])).
fof(p4, plain, 'P'(s(s('0'))) => 'P'(s(s('0'))), inference(logical_axiom, [status(thm)], [])).
fof(p5, plain, (('P'(s('0')) => 'P'(s(s('0')))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s('0'))), inference(imp_left, [status(thm)], [p3, p4])).
fof(p6, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s('0'))), inference(forall_left, [status(thm)], [p5])).
fof(p7, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s('0'))), inference(contraction_left, [status(thm)], [p6])).
fof(p8, plain, 'P'(s(s(s('0')))) => 'P'(s(s(s('0')))), inference(logical_axiom, [status(thm)], [])).
fof(p9, plain, (('P'(s(s('0'))) => 'P'(s(s(s('0'))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s('0')))), inference(imp_left, [status(thm)], [p7, p8])).
fof(p10, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s('0')))), inference(forall_left, [status(thm)], [p9])).
fof(p11, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s('0')))), inference(contraction_left, [status(thm)], [p10])).
fof(p12, plain, 'P'(s(s(s(s('0'))))) => 'P'(s(s(s(s('0'))))), inference(logical_axiom, [status(thm)], [])).
fof(p13, plain, (('P'(s(s(s('0')))) => 'P'(s(s(s(s('0')))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s('0'))))), inference(imp_left, [status(thm)], [p11, p12])).
fof(p14, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s('0'))))), inference(forall_left, [status(thm)], [p13])).
fof(p15, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s('0'))))), inference(contraction_left, [status(thm)], [p14])).
fof(p16, plain, 'P'(s(s(s(s(s('0')))))) => 'P'(s(s(s(s(s('0')))))), inference(logical_axiom, [status(thm)], [])).
fof(p17, plain, (('P'(s(s(s(s('0'))))) => 'P'(s(s(s(s(s('0'))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s('0')))))), inference(imp_left, [status(thm)], [p15, p16])).
fof(p18, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s('0')))))), inference(forall_left, [status(thm)], [p17])).
fof(p19, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s('0')))))), inference(contraction_left, [status(thm)], [p18])).
fof(p20, plain, 'P'(s(s(s(s(s(s('0'))))))) => 'P'(s(s(s(s(s(s('0'))))))), inference(logical_axiom, [status(thm)], [])).
fof(p21, plain, (('P'(s(s(s(s(s('0')))))) => 'P'(s(s(s(s(s(s('0')))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s('0'))))))), inference(imp_left, [status(thm)], [p19, p20])).
fof(p22, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s('0'))))))), inference(forall_left, [status(thm)], [p21])).
fof(p23, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s('0'))))))), inference(contraction_left, [status(thm)], [p22])).
fof(p24, plain, 'P'(s(s(s(s(s(s(s('0')))))))) => 'P'(s(s(s(s(s(s(s('0')))))))), inference(logical_axiom, [status(thm)], [])).
fof(p25, plain, (('P'(s(s(s(s(s(s('0'))))))) => 'P'(s(s(s(s(s(s(s('0'))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s('0')))))))), inference(imp_left, [status(thm)], [p23, p24])).
fof(p26, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s('0')))))))), inference(forall_left, [status(thm)], [p25])).
fof(p27, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s('0')))))))), inference(contraction_left, [status(thm)], [p26])).
fof(p28, plain, 'P'(s(s(s(s(s(s(s(s('0'))))))))) => 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p29, plain, (('P'(s(s(s(s(s(s(s('0')))))))) => 'P'(s(s(s(s(s(s(s(s('0')))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(imp_left, [status(thm)], [p27, p28])).
fof(p30, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(forall_left, [status(thm)], [p29])).
fof(p31, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(contraction_left, [status(thm)], [p30])).
fof(p32, plain, 'P'(s(s(s(s(s(s(s(s(s('0')))))))))) => 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p33, plain, (('P'(s(s(s(s(s(s(s(s('0'))))))))) => 'P'(s(s(s(s(s(s(s(s(s('0'))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(imp_left, [status(thm)], [p31, p32])).
fof(p34, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(forall_left, [status(thm)], [p33])).
fof(p35, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(contraction_left, [status(thm)], [p34])).
fof(p36, plain, 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p37, plain, (('P'(s(s(s(s(s(s(s(s(s('0')))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s('0')))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(imp_left, [status(thm)], [p35, p36])).
fof(p38, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(forall_left, [status(thm)], [p37])).
fof(p39, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(contraction_left, [status(thm)], [p38])).
fof(p40, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p41, plain, (('P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(imp_left, [status(thm)], [p39, p40])).
fof(p42, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(forall_left, [status(thm)], [p41])).
fof(p43, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(contraction_left, [status(thm)], [p42])).
fof(p44, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p45, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(imp_left, [status(thm)], [p43, p44])).
fof(p46, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(forall_left, [status(thm)], [p45])).
fof(p47, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(contraction_left, [status(thm)], [p46])).
fof(p48, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p49, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(imp_left, [status(thm)], [p47, p48])).
fof(p50, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(forall_left, [status(thm)], [p49])).
fof(p51, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(contraction_left, [status(thm)], [p50])).
fof(p52, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p53, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(imp_left, [status(thm)], [p51, p52])).
fof(p54, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(forall_left, [status(thm)], [p53])).
fof(p55, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(contraction_left, [status(thm)], [p54])).
fof(p56, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p57, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(imp_left, [status(thm)], [p55, p56])).
fof(p58, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(forall_left, [status(thm)], [p57])).
fof(p59, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(contraction_left, [status(thm)], [p58])).
fof(p60, plain, ~ (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')), inference(neg_left, [status(thm)], [p59])).
fof(p61, plain, (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => $false, inference(weakening_right, [status(thm)], [p60])).
fof(acut0, plain, (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) & 'P'('0')) => $false, inference(cut, [status(thm)], [p61, a0])).
fof(acut1, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) => $false, inference(cut, [status(thm)], [acut0, a1])).
fof(nc_cut, plain, $false, inference(cut, [status(thm)], [acut1, nc])).
