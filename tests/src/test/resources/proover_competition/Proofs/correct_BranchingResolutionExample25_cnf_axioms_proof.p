cnf(p0, axiom, p(s('0')), file('Problems/BranchingResolutionExample25_cnf_axioms.p', ax1)).
cnf(p1, axiom, p('0'), file('Problems/BranchingResolutionExample25_cnf_axioms.p',ax2)).
cnf(p2, axiom, ~ p(X) | ~ p(s(X)) | p(s(s(X))), file('Problems/BranchingResolutionExample25_cnf_axioms.p',ax3)).
cnf(p3, plain, ~ p('0') | ~ p(s('0')) | p(s(s('0'))), inference(subst, [status(thm)], [p2])).
cnf(p4, plain, ~ p(s('0')) | p(s(s('0'))), inference(resolution, [status(thm)], [p1, p3])).
cnf(p5, plain, p(s(s('0'))), inference(resolution, [status(thm)], [p0, p4])).
cnf(p6, plain, ~ p(s('0')) | ~ p(s(s('0'))) | p(s(s(s('0')))), inference(subst, [status(thm)], [p2])).
cnf(p7, plain, ~ p(s(s('0'))) | p(s(s(s('0')))), inference(resolution, [status(thm)], [p0, p6])).
cnf(p8, plain, p(s(s(s('0')))), inference(resolution, [status(thm)], [p5, p7])).
cnf(p9, plain, ~ p(s(s('0'))) | ~ p(s(s(s('0')))) | p(s(s(s(s('0'))))), inference(subst, [status(thm)], [p2])).
cnf(p10, plain, ~ p(s(s(s('0')))) | p(s(s(s(s('0'))))), inference(resolution, [status(thm)], [p5, p9])).
cnf(p11, plain, p(s(s(s(s('0'))))), inference(resolution, [status(thm)], [p8, p10])).
cnf(p12, plain, ~ p(s(s(s('0')))) | ~ p(s(s(s(s('0'))))) | p(s(s(s(s(s('0')))))), inference(subst, [status(thm)], [p2])).
cnf(p13, plain, ~ p(s(s(s(s('0'))))) | p(s(s(s(s(s('0')))))), inference(resolution, [status(thm)], [p8, p12])).
cnf(p14, plain, p(s(s(s(s(s('0')))))), inference(resolution, [status(thm)], [p11, p13])).
cnf(p15, plain, ~ p(s(s(s(s('0'))))) | ~ p(s(s(s(s(s('0')))))) | p(s(s(s(s(s(s('0'))))))), inference(subst, [status(thm)], [p2])).
cnf(p16, plain, ~ p(s(s(s(s(s('0')))))) | p(s(s(s(s(s(s('0'))))))), inference(resolution, [status(thm)], [p11, p15])).
cnf(p17, plain, p(s(s(s(s(s(s('0'))))))), inference(resolution, [status(thm)], [p14, p16])).
cnf(p18, plain, ~ p(s(s(s(s(s('0')))))) | ~ p(s(s(s(s(s(s('0'))))))) | p(s(s(s(s(s(s(s('0')))))))), inference(subst, [status(thm)], [p2])).
cnf(p19, plain, ~ p(s(s(s(s(s(s('0'))))))) | p(s(s(s(s(s(s(s('0')))))))), inference(resolution, [status(thm)], [p14, p18])).
cnf(p20, plain, p(s(s(s(s(s(s(s('0')))))))), inference(resolution, [status(thm)], [p17, p19])).
cnf(p21, plain, ~ p(s(s(s(s(s(s('0'))))))) | ~ p(s(s(s(s(s(s(s('0')))))))) | p(s(s(s(s(s(s(s(s('0'))))))))), inference(subst, [status(thm)], [p2])).
cnf(p22, plain, ~ p(s(s(s(s(s(s(s('0')))))))) | p(s(s(s(s(s(s(s(s('0'))))))))), inference(resolution, [status(thm)], [p17, p21])).
cnf(p23, plain, p(s(s(s(s(s(s(s(s('0'))))))))), inference(resolution, [status(thm)], [p20, p22])).
cnf(p24, plain, ~ p(s(s(s(s(s(s(s('0')))))))) | ~ p(s(s(s(s(s(s(s(s('0'))))))))) | p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(subst, [status(thm)], [p2])).
cnf(p25, plain, ~ p(s(s(s(s(s(s(s(s('0'))))))))) | p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(resolution, [status(thm)], [p20, p24])).
cnf(p26, plain, p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(resolution, [status(thm)], [p23, p25])).
cnf(p27, plain, ~ p(s(s(s(s(s(s(s(s('0'))))))))) | ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p28, plain, ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(resolution, [status(thm)], [p23, p27])).
cnf(p29, plain, p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(resolution, [status(thm)], [p26, p28])).
cnf(p30, plain, ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p31, plain, ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(resolution, [status(thm)], [p26, p30])).
cnf(p32, plain, p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(resolution, [status(thm)], [p29, p31])).
cnf(p33, plain, ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p34, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(resolution, [status(thm)], [p29, p33])).
cnf(p35, plain, p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(resolution, [status(thm)], [p32, p34])).
cnf(p36, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p37, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(resolution, [status(thm)], [p32, p36])).
cnf(p38, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(resolution, [status(thm)], [p35, p37])).
cnf(p39, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p40, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(resolution, [status(thm)], [p35, p39])).
cnf(p41, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(resolution, [status(thm)], [p38, p40])).
cnf(p42, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p43, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(resolution, [status(thm)], [p38, p42])).
cnf(p44, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(resolution, [status(thm)], [p41, p43])).
cnf(p45, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p46, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(resolution, [status(thm)], [p41, p45])).
cnf(p47, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(resolution, [status(thm)], [p44, p46])).
cnf(p48, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p49, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(resolution, [status(thm)], [p44, p48])).
cnf(p50, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(resolution, [status(thm)], [p47, p49])).
cnf(p51, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p52, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(resolution, [status(thm)], [p47, p51])).
cnf(p53, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(resolution, [status(thm)], [p50, p52])).
cnf(p54, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p55, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(resolution, [status(thm)], [p50, p54])).
cnf(p56, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(resolution, [status(thm)], [p53, p55])).
cnf(p57, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p58, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(resolution, [status(thm)], [p53, p57])).
cnf(p59, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(resolution, [status(thm)], [p56, p58])).
cnf(p60, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p61, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(resolution, [status(thm)], [p56, p60])).
cnf(p62, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(resolution, [status(thm)], [p59, p61])).
cnf(p63, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p64, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(resolution, [status(thm)], [p59, p63])).
cnf(p65, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(resolution, [status(thm)], [p62, p64])).
cnf(p66, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p67, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(resolution, [status(thm)], [p62, p66])).
cnf(p68, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(resolution, [status(thm)], [p65, p67])).
cnf(p69, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p70, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(resolution, [status(thm)], [p65, p69])).
cnf(p71, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(resolution, [status(thm)], [p68, p70])).
cnf(p72, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(subst, [status(thm)], [p2])).
cnf(p73, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(resolution, [status(thm)], [p68, p72])).
cnf(p74, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(resolution, [status(thm)], [p71, p73])).
cnf(p75, axiom, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))),file('Problems/BranchingResolutionExample25_cnf_axioms.p',final)).
cnf(p76, plain, $false, inference(resolution, [status(thm)], [p74, p75])).
