fof(a0, axiom, ![X]: ('P'(X) => 'P'(s(X))), file('Problems/linear_example_26.p', a0)).
fof(a1, axiom, 'P'('0'), file('Problems/linear_example_26.p', a1)).
fof(c, conjecture, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), file('Problems/linear_example_26.p', c)).
fof(nc, negated_conjecture, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(negated_conjecture, [status(cth)], [c])).
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
fof(p60, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p61, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(imp_left, [status(thm)], [p59, p60])).
fof(p62, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(forall_left, [status(thm)], [p61])).
fof(p63, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(contraction_left, [status(thm)], [p62])).
fof(p64, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p65, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(imp_left, [status(thm)], [p63, p64])).
fof(p66, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(forall_left, [status(thm)], [p65])).
fof(p67, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(contraction_left, [status(thm)], [p66])).
fof(p68, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p69, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(imp_left, [status(thm)], [p67, p68])).
fof(p70, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(forall_left, [status(thm)], [p69])).
fof(p71, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(contraction_left, [status(thm)], [p70])).
fof(p72, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p73, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(imp_left, [status(thm)], [p71, p72])).
fof(p74, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(forall_left, [status(thm)], [p73])).
fof(p75, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(contraction_left, [status(thm)], [p74])).
fof(p76, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p77, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(imp_left, [status(thm)], [p75, p76])).
fof(p78, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(forall_left, [status(thm)], [p77])).
fof(p79, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(contraction_left, [status(thm)], [p78])).
fof(p80, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p81, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(imp_left, [status(thm)], [p79, p80])).
fof(p82, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(forall_left, [status(thm)], [p81])).
fof(p83, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(contraction_left, [status(thm)], [p82])).
fof(p84, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p85, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(imp_left, [status(thm)], [p83, p84])).
fof(p86, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(forall_left, [status(thm)], [p85])).
fof(p87, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(contraction_left, [status(thm)], [p86])).
fof(p88, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p89, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(imp_left, [status(thm)], [p87, p88])).
fof(p90, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(forall_left, [status(thm)], [p89])).
fof(p91, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(contraction_left, [status(thm)], [p90])).
fof(p92, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p93, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(imp_left, [status(thm)], [p91, p92])).
fof(p94, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(forall_left, [status(thm)], [p93])).
fof(p95, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(contraction_left, [status(thm)], [p94])).
fof(p96, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p97, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(imp_left, [status(thm)], [p95, p96])).
fof(p98, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(forall_left, [status(thm)], [p97])).
fof(p99, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(contraction_left, [status(thm)], [p98])).
fof(p100, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(logical_axiom, [status(thm)], [])).
fof(p101, plain, (('P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(imp_left, [status(thm)], [p99, p100])).
fof(p102, plain, (![X]: ('P'(X) => 'P'(s(X))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(forall_left, [status(thm)], [p101])).
fof(p103, plain, (![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(contraction_left, [status(thm)], [p102])).
fof(p104, plain, ~ (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')), inference(neg_left, [status(thm)], [p103])).
fof(p105, plain, (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) & ![X]: ('P'(X) => 'P'(s(X))) & 'P'('0')) => $false, inference(weakening_right, [status(thm)], [p104])).
fof(acut0, plain, (~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) & 'P'('0')) => $false, inference(cut, [status(thm)], [p105, a0])).
fof(acut1, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))) => $false, inference(cut, [status(thm)], [acut0, a1])).
fof(nc_cut, plain, $false, inference(cut, [status(thm)], [acut1, nc])).
