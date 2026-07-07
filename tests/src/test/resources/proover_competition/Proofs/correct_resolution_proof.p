cnf(p0, axiom, 'P'('0'), file('Problems/correct_resolution.p', a0)).
fof(p1, plain, 'P'('0'), inference(subst, [status(thm)], [p0])).
fof(p2, axiom, ![X]: ('P'(X) => 'P'(s(X))), file('Problems/correct_resolution.p', a1)).
fof(p3, plain, ![X]: ('P'(X) => 'P'(s(X))), inference(all_r, [status(thm)], [p2])).
fof(p4, plain, ![X]: (~ 'P'(X) | 'P'(s(X))), inference(imp_r, [status(thm)], [p3])).
fof(p5, plain, ~ 'P'('0') | 'P'(s('0')), inference(subst, [status(thm)], [p4])).
fof(p6, plain, 'P'(s('0')), inference(resolution, [status(thm)], [p1, p5])).
fof(p7, plain, 'P'(s('0')), inference(subst, [status(thm)], [p6])).
fof(p8, plain, ~ 'P'(s('0')) | 'P'(s(s('0'))), inference(subst, [status(thm)], [p4])).
fof(p9, plain, 'P'(s(s('0'))), inference(resolution, [status(thm)], [p7, p8])).
fof(p10, plain, 'P'(s(s('0'))), inference(subst, [status(thm)], [p9])).
fof(p11, plain, ~ 'P'(s(s('0'))) | 'P'(s(s(s('0')))), inference(subst, [status(thm)], [p4])).
fof(p12, plain, 'P'(s(s(s('0')))), inference(resolution, [status(thm)], [p10, p11])).
fof(p13, plain, 'P'(s(s(s('0')))), inference(subst, [status(thm)], [p12])).
fof(p14, plain, ~ 'P'(s(s(s('0')))) | 'P'(s(s(s(s('0'))))), inference(subst, [status(thm)], [p4])).
fof(p15, plain, 'P'(s(s(s(s('0'))))), inference(resolution, [status(thm)], [p13, p14])).
fof(p16, plain, 'P'(s(s(s(s('0'))))), inference(subst, [status(thm)], [p15])).
fof(p17, plain, ~ 'P'(s(s(s(s('0'))))) | 'P'(s(s(s(s(s('0')))))), inference(subst, [status(thm)], [p4])).
fof(p18, plain, 'P'(s(s(s(s(s('0')))))), inference(resolution, [status(thm)], [p16, p17])).
fof(p19, plain, 'P'(s(s(s(s(s('0')))))), inference(subst, [status(thm)], [p18])).
fof(p20, plain, ~ 'P'(s(s(s(s(s('0')))))) | 'P'(s(s(s(s(s(s('0'))))))), inference(subst, [status(thm)], [p4])).
fof(p21, plain, 'P'(s(s(s(s(s(s('0'))))))), inference(resolution, [status(thm)], [p19, p20])).
fof(p22, plain, 'P'(s(s(s(s(s(s('0'))))))), inference(subst, [status(thm)], [p21])).
fof(p23, plain, ~ 'P'(s(s(s(s(s(s('0'))))))) | 'P'(s(s(s(s(s(s(s('0')))))))), inference(subst, [status(thm)], [p4])).
fof(p24, plain, 'P'(s(s(s(s(s(s(s('0')))))))), inference(resolution, [status(thm)], [p22, p23])).
fof(p25, plain, 'P'(s(s(s(s(s(s(s('0')))))))), inference(subst, [status(thm)], [p24])).
fof(p26, plain, ~ 'P'(s(s(s(s(s(s(s('0')))))))) | 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(subst, [status(thm)], [p4])).
fof(p27, plain, 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(resolution, [status(thm)], [p25, p26])).
fof(p28, plain, 'P'(s(s(s(s(s(s(s(s('0'))))))))), inference(subst, [status(thm)], [p27])).
fof(p29, plain, ~ 'P'(s(s(s(s(s(s(s(s('0'))))))))) | 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(subst, [status(thm)], [p4])).
fof(p30, plain, 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(resolution, [status(thm)], [p28, p29])).
fof(p31, plain, 'P'(s(s(s(s(s(s(s(s(s('0')))))))))), inference(subst, [status(thm)], [p30])).
fof(p32, plain, ~ 'P'(s(s(s(s(s(s(s(s(s('0')))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(subst, [status(thm)], [p4])).
fof(p33, plain, 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(resolution, [status(thm)], [p31, p32])).
fof(p34, plain, 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(subst, [status(thm)], [p33])).
fof(p35, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(subst, [status(thm)], [p4])).
fof(p36, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(resolution, [status(thm)], [p34, p35])).
fof(p37, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(subst, [status(thm)], [p36])).
fof(p38, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p39, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(resolution, [status(thm)], [p37, p38])).
fof(p40, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(subst, [status(thm)], [p39])).
fof(p41, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p42, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(resolution, [status(thm)], [p40, p41])).
fof(p43, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(subst, [status(thm)], [p42])).
fof(p44, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p45, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(resolution, [status(thm)], [p43, p44])).
fof(p46, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(subst, [status(thm)], [p45])).
fof(p47, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p48, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(resolution, [status(thm)], [p46, p47])).
fof(p49, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(subst, [status(thm)], [p48])).
fof(p50, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p51, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(resolution, [status(thm)], [p49, p50])).
fof(p52, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(subst, [status(thm)], [p51])).
fof(p53, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p54, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(resolution, [status(thm)], [p52, p53])).
fof(p55, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(subst, [status(thm)], [p54])).
fof(p56, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p57, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(resolution, [status(thm)], [p55, p56])).
fof(p58, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(subst, [status(thm)], [p57])).
fof(p59, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p60, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(resolution, [status(thm)], [p58, p59])).
fof(p61, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(subst, [status(thm)], [p60])).
fof(p62, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p63, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(resolution, [status(thm)], [p61, p62])).
fof(p64, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(subst, [status(thm)], [p63])).
fof(p65, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p66, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(resolution, [status(thm)], [p64, p65])).
fof(p67, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(subst, [status(thm)], [p66])).
fof(p68, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p69, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(resolution, [status(thm)], [p67, p68])).
fof(p70, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(subst, [status(thm)], [p69])).
fof(p71, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p72, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(resolution, [status(thm)], [p70, p71])).
fof(p73, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(subst, [status(thm)], [p72])).
fof(p74, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p75, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(resolution, [status(thm)], [p73, p74])).
fof(p76, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(subst, [status(thm)], [p75])).
fof(p77, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p78, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(resolution, [status(thm)], [p76, p77])).
fof(p79, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(subst, [status(thm)], [p78])).
fof(p80, plain, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))) | 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(subst, [status(thm)], [p4])).
fof(p81, plain, 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), inference(resolution, [status(thm)], [p79, p80])).
cnf(p82, axiom, ~ 'P'(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))), file('Problems/correct_resolution.p', a2)).
fof(p83, plain, $false, inference(resolution, [status(thm)], [p81, p82])).
