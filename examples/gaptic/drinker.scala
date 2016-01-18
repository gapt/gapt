import at.logic.gapt.expr.FOLVar
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

val drinker = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  use(exR( parseTerm( "c" ), "D1" ))
  use(impR( "D1" ))
  use(allR( FOLVar( "y_0" ), "D1_2" ))
  use(exR( parseTerm( "y_0" ), "D2" ))
  use(impR( "D2" ))
  use(allR( FOLVar( "y_1" ), "D2_2" ))
  use(axiomLog  )
} qed

val dualdrinker = new Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))")), Nil )) {
  use(allL( parseTerm( "c" ), "D1" ))
  use(andL( "D1" ))
  use(exL( FOLVar( "y_0" ) ))
  use(negL( "D1_2" ))
  use(allL( parseTerm( "y_0" ), "D2" ))
  use(andL( "D2" ))
  use(exL( FOLVar( "y_1" ) ))
  use(negL( "D2_2" ))
  use(axiomLog)
} qed

val drinker2 = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  use(exR( parseTerm( "c" ), "D1" ))
  use(impR)
  use(allR)
  use(exR( parseTerm( "y" ), "D2" ))
  use(impR)
  use(allR)
  use(axiomLog)
} qed

val drinker3 = new Lemma( Sequent( Nil, Seq( "D" -> parseFormula( "(exists x (P(x) -> (all y P(y))))" )))) {
  use(exR( parseTerm( "c" ), "D1" ))
  use(impR)
  use(allR)
  use(exR( parseTerm( "y" ), "D2" ))
  use(impR)
  use(allR)
  use(axiom)
} qed

val dualdrinker2 = new Lemma( Sequent( Seq( "D" -> parseFormula( "(all x (P(x) & (exists y -P(y))))")), Nil )) {
  use(allL( parseTerm( "c" ), "D1" ))
  use(andL)
  use(exL)
  use(negL)
  use(allL( parseTerm( "y" ), "D2" ))
  use(andL)
  use(exL)
  use(negL)
  use(axiomLog)
} qed