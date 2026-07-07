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
cnf(p19, axiom, ~ 'P'(s(s(s(s(s('0')))))), file('Problems/correct_resolution.p', a2)).
fof(p20, plain, $false, inference(resolution, [status(thm)], [p18, p19])).
