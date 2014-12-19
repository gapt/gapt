{z <- \lambda k. a }

g(0,x) -> x
g(k+1,x) -> f(g(k,x))

\rho_1(0,z) -> |-
\rho_1(k+1,z) -> r( \rho_2(k+1,z) ; P(f(g(k+1,a))) |- ; P(f(g(k+1,a))) )

\rho_2(0,z) ->  r(|-P(a); P(z(0)) |- P(f(g(0,z(0)))); P(a) )
\rho_2(k+1,z) -> r( \rho_2(k,z) ; P(g(k+1,z(k+1)))|-P(f(g(k+1,z(k+1)))) ; P(g(k+1,z(k+1))))
