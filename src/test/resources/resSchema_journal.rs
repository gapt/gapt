{z <- \lambda k. g(m(k),a) }

m(0) -> 0
m(k+1) -> k

g(0,x) -> x
g(k+1,x) -> f(g(k,x))

\rho_1(0,z) -> r( |-P(a) ; P(g(0,a))|- ; P(g(0,a)) )
\rho_1(k+1,z) -> r( \rho_2(k+1,z) ; P(g(k+1,a))|- ; P(g(k+1,a)) )

\rho_2(0,z) ->  |-P(a)
\rho_2(k+1,z) -> r( \rho_2(k,z) ; P(z(k+1))|-P(f(z(k+1))) ; P(g(k,a)))
