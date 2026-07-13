fof(p0, axiom, p(s('0')), file('Problems/BranchingResolutionExample25_closed_axioms.p', ax1)).
fof(p1, axiom, p('0'), file('Problems/BranchingResolutionExample25_closed_axioms.p', ax2)).
fof(p2, axiom, ![X]: ((p(X) & p(s(X))) => p(s(s(X)))), file('Problems/BranchingResolutionExample25_closed_axioms.p', ax3)).
fof(p3, plain, ![X]: ((p(X) & p(s(X))) => p(s(s(X)))), inference(all_r, [status(thm)], [p2])).
fof(p4, plain, ![X]: (~ (p(X) & p(s(X))) | p(s(s(X)))), inference(imp_r, [status(thm)], [p3])).
fof(p5, plain, ![X]: (~ p(X) | ~ p(s(X)) | p(s(s(X)))), inference(and_l, [status(thm)], [p4])).
fof(p6, plain, ~ p('0') | ~ p(s('0')) | p(s(s('0'))), inference(subst, [status(thm)], [p5])).
fof(p7, plain, ~ p(s('0')) | p(s(s('0'))), inference(resolution, [status(thm)], [p1, p6])).
fof(p8, plain, p(s(s('0'))), inference(resolution, [status(thm)], [p0, p7])).
fof(p9, plain, ~ p(s('0')) | ~ p(s(s('0'))) | p(s(s(s('0')))), inference(subst, [status(thm)], [p5])).
fof(p10, plain, ~ p(s(s('0'))) | p(s(s(s('0')))), inference(resolution, [status(thm)], [p0, p9])).
fof(p11, plain, p(s(s(s('0')))), inference(resolution, [status(thm)], [p8, p10])).
fof(p12, plain, ~ p(s(s('0'))) | ~ p(s(s(s('0')))) | p(s(s(s(s('0'))))), inference(subst, [status(thm)], [p5])).
fof(p13, plain, ~ p(s(s(s('0')))) | p(s(s(s(s('0'))))), inference(resolution, [status(thm)], [p8, p12])).
fof(p14, plain, p(s(s(s(s('0'))))), inference(resolution, [status(thm)], [p11, p13])).
fof(p15, plain, ~ p(s(s(s('0')))) | ~ p(s(s(s(s('0'))))) | p(s(s(s(s(s('0')))))), inference(subst, [status(thm)], [p5])).
fof(p16, plain, ~ p(s(s(s(s('0'))))) | p(s(s(s(s(s('0')))))), inference(resolution, [status(thm)], [p11, p15])).
fof(p17, plain, p(s(s(s(s(s('0')))))), inference(resolution, [status(thm)], [p14, p16])).
fof(p18, plain, ~ p(s(s(s(s('0'))))) | ~ p(s(s(s(s(s('0')))))) | p(s(s(s(s(s(s('0'))))))), inference(subst, [status(thm)], [p5])).
fof(p19, plain, ~ p(s(s(s(s(s('0')))))) | p(s(s(s(s(s(s('0'))))))), inference(resolution, [status(thm)], [p14, p18])).
fof(p20, plain, p(s(s(s(s(s(s('0'))))))), inference(resolution, [status(thm)], [p17, p19])).
fof(p21, plain, ~ p(s(s(s(s(s('0')))))) | ~ p(s(s(s(s(s(s('0'))))))) | p(s(s(s(s(s(s(s('0')))))))), inference(subst, [status(thm)], [p5])).
fof(p22, plain, ~ p(s(s(s(s(s(s('0'))))))) | p(s(s(s(s(s(s(s('0')))))))), inference(resolution, [status(thm)], [p17, p21])).
fof(p23, plain, p(s(s(s(s(s(s(s('0')))))))), inference(resolution, [status(thm)], [p20, p22])).
fof(p24, plain, ~ p(s(s(s(s(s(s('0'))))))) | ~ p(s(s(s(s(s(s(s('0')))))))) | p(s(s(s(s(s(s(s(s('0'))))))))), inference(subst, [status(thm)], [p5])).
fof(p25, plain, ~ p(s(s(s(s(s(s(s('0')))))))) | p(s(s(s(s(s(s(s(s('0'))))))))), inference(resolution, [status(thm)], [p20, p24])).
fof(p26, plain, p(s(s(s(s(s(s(s(s('0'))))))))), inference(resolution, [status(thm)], [p23, p25])).
fof(p27, plain, ~ p(s(s(s(s(s(s(s('0')))))))) | ~ p(s(s(s(s(s(s(s(s('0'))))))))) | p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(subst, [status(thm)], [p5])).
fof(p28, plain, ~ p(s(s(s(s(s(s(s(s('0'))))))))) | p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(resolution, [status(thm)], [p23, p27])).
fof(p29, plain, p(s(s(s(s(s(s(s(s(s('0')))))))))), inference(resolution, [status(thm)], [p26, p28])).
fof(p30, plain, ~ p(s(s(s(s(s(s(s(s('0'))))))))) | ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(subst, [status(thm)], [p5])).
fof(p31, plain, ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(resolution, [status(thm)], [p26, p30])).
fof(p32, plain, p(s(s(s(s(s(s(s(s(s(s('0'))))))))))), inference(resolution, [status(thm)], [p29, p31])).
fof(p33, plain, ~ p(s(s(s(s(s(s(s(s(s('0')))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(subst, [status(thm)], [p5])).
fof(p34, plain, ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(resolution, [status(thm)], [p29, p33])).
fof(p35, plain, p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))), inference(resolution, [status(thm)], [p32, p34])).
fof(p36, plain, ~ p(s(s(s(s(s(s(s(s(s(s('0'))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p37, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(resolution, [status(thm)], [p32, p36])).
fof(p38, plain, p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))), inference(resolution, [status(thm)], [p35, p37])).
fof(p39, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p40, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(resolution, [status(thm)], [p35, p39])).
fof(p41, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))), inference(resolution, [status(thm)], [p38, p40])).
fof(p42, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p43, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(resolution, [status(thm)], [p38, p42])).
fof(p44, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))), inference(resolution, [status(thm)], [p41, p43])).
fof(p45, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p46, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(resolution, [status(thm)], [p41, p45])).
fof(p47, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))), inference(resolution, [status(thm)], [p44, p46])).
fof(p48, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p49, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(resolution, [status(thm)], [p44, p48])).
fof(p50, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))), inference(resolution, [status(thm)], [p47, p49])).
fof(p51, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p52, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(resolution, [status(thm)], [p47, p51])).
fof(p53, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))), inference(resolution, [status(thm)], [p50, p52])).
fof(p54, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p55, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(resolution, [status(thm)], [p50, p54])).
fof(p56, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))), inference(resolution, [status(thm)], [p53, p55])).
fof(p57, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p58, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(resolution, [status(thm)], [p53, p57])).
fof(p59, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))), inference(resolution, [status(thm)], [p56, p58])).
fof(p60, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p61, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(resolution, [status(thm)], [p56, p60])).
fof(p62, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))), inference(resolution, [status(thm)], [p59, p61])).
fof(p63, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p64, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(resolution, [status(thm)], [p59, p63])).
fof(p65, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))), inference(resolution, [status(thm)], [p62, p64])).
fof(p66, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p67, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(resolution, [status(thm)], [p62, p66])).
fof(p68, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))), inference(resolution, [status(thm)], [p65, p67])).
fof(p69, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p70, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(resolution, [status(thm)], [p65, p69])).
fof(p71, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))), inference(resolution, [status(thm)], [p68, p70])).
fof(p72, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p73, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(resolution, [status(thm)], [p68, p72])).
fof(p74, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))), inference(resolution, [status(thm)], [p71, p73])).
fof(p75, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))) | ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(subst, [status(thm)], [p5])).
fof(p76, plain, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))) | p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(resolution, [status(thm)], [p71, p75])).
fof(p77, plain, p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), inference(resolution, [status(thm)], [p74, p76])).
fof(p78, axiom, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0')))))))))))))))))))))))))), file('Problems/BranchingResolutionExample25_closed_axioms.p', c)).
fof(p79, plain, $false, inference(resolution, [status(thm)], [p77, p78])).
