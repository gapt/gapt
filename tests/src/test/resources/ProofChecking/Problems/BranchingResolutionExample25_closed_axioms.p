cnf(ax1, axiom, p(s('0'))).
cnf(ax2, axiom, p('0')).
fof(ax3, axiom, ![X]: ((p(X) & p(s(X))) => p(s(s(X))))).
cnf(c, axiom, ~ p(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s('0'))))))))))))))))))))))))))).
