import at.logic.gapt.proofs.gaptic._

val A = parseFormula( "(all x ( f(x) = 0 | f(x) = 1 ))" )
val I0 = parseFormula( "(all x exists y f( x + y ) = 0)" )
val I1 = parseFormula( "(all x exists y f( x + y ) = 1)" )
val Iv = parseFormula( "(all x exists y f( x + y ) = v)" )

val lhs = new Lemma( Sequent( Seq( "A" -> parseFormula( "A" )), Seq( "I0" -> parseFormula( "I(0)" ), "I1" -> parseFormula( "I(1)" )))) {
  use(defR( "I0", I0 ))
  use(defR( "I1", I1 ))
  use(allR( FOLVar( "x_0" ), "I0" ))
  use(allR( FOLVar( "x_1" ), "I1" ))
  use(exR( parseTerm( "x_0" ), "I1'", "I1" ))
  use(forget( "I1" ))
  use(exR( parseTerm( "x_1" ), "I0'", "I0" ))
  use(forget( "I0" ))
  use(defL( "A", A ))
  use(allL( parseTerm( "x_0 + x_1" ), "A'", "A" ))
  use(forget( "A" ))
  use(destruct)
  use(axiom)
  use(forget( "I0'" ))
  use(axiomTh)
} qed

val rhs = new Lemma( Sequent( Seq( "Iv" -> parseFormula( "I(v)" )), Seq( "C" -> parseFormula( "(exists x exists y ( -x=y & f(x)=f(y) ))" )))) {
  use(defL( "Iv", Iv ))
  use(allL( parseTerm( "0" ), "Iv1", "Iv" ))
  use(exL( FOLVar( "y_0" ), "Iv1" ))
  use(allL( parseTerm( "y_0 + 1" ), "Iv2", "Iv" ))
  use(forget( "Iv" ))
  use(exL( FOLVar( "y_1" ), "Iv2" ))
  use(exR( parseTerm( "y_0" ), "C'", "C" ))
  use(exR( parseTerm( "(y_0 + y_1) + 1" ), "C''", "C'"))
  use(forget( "C" ))
  use(forget( "C'" ))
  use(destruct)
  use(negR)
  use(forget( "Iv1" ))
  use(forget( "Iv2" ))
  use(axiomTh)
  use(eqL( "Iv2", "Iv1" ))
  use(forget( "Iv2" ))
  use(axiomTh)
} qed

val p = new Lemma( Sequent( Seq( "A" -> parseFormula( "A" )), Seq( "C" -> parseFormula( "(exists x exists y ( -x=y & f(x)=f(y) ))" )))) {
  use(cut( parseFormula( "I(1)" ), "I1" ))
  use(cut( parseFormula( "I(0)" ), "I0" ))
  use(forget( "C" )) // should not be necessary
  use(insert( lhs ))
  use(forget( "A" ))
  use(forget( "I1" ))
/*
  use(insert( rhs )) // script fails here - why?
*/
} qed
