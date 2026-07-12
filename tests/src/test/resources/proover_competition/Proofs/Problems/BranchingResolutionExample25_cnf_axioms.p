cnf(ax1, axiom, p(s('0'))).
cnf(ax2, axiom, p('0')).
cnf(ax3, axiom, ~ p(X) | ~ p(s(X)) | p(s(s(X)))).
cnf(final, axiom, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))).
