package at.logic.gapt.examples.tip.grammars

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object simp_expr_unambig1 extends TacticsProof {

  val bench = def_simp_expr_unambig1.loadProblem
  ctx = bench.ctx

  val theory = Sequent(
    bench.toSequent.antecedent.zipWithIndex.map { case ( f, i ) => s"h$i" -> f },
    Nil )

  val sequent = theory ++ Sequent(
    Nil,
    bench.toSequent.succedent.map { case f => "goal" -> f } )

  val cong_pos = (
    ( "h1" -> hof"!x0 !x1 tail(cons(x0, x1)) = x1" ) +:
    ( "ass" -> hof"cons(z,x) = cons(z,y)" ) +:
    Sequent() :+
    ( "conc" -> hof"(x:list) = y" ) )
  val cong_pos_proof = Lemma( cong_pos ) {
    allL( "h1", hov"z:Tok", hov"x:list" )
    allL( "h1", hov"z:Tok", hov"y:list" )
    quasiprop
  }

  val cong_neg = (
    ( "h0" -> hof"!x0 !x1 head(cons(x0, x1)) = x0" ) +:
    ( "ass" -> hof"- ( ( u:Tok ) = v )" ) +:
    ( "conc" -> hof"cons(u,x) = cons(v,y)" ) +:
    Sequent() )
  val cong_neg_proof = Lemma( cong_neg ) {
    allL( "h0", hov"u:Tok", hov"x:list" )
    allL( "h0", hov"v:Tok", hov"y:list" )
    quasiprop
  }

  // the symmetric variant cong_neg_symm of cong_neg is necessary for the insert-tactic to work properly (FIXME?)
  val cong_neg_symm = (
    ( "h0" -> hof"!x0 !x1 head(cons(x0, x1)) = x0" ) +:
    ( "ass" -> hof"- ( ( v:Tok ) = u )" ) +:
    ( "conc" -> hof"cons(u,x) = cons(v,y)" ) +:
    Sequent() )
  val cong_neg_symm_proof = Lemma( cong_neg_symm ) {
    allL( "h0", hov"u:Tok", hov"x:list" )
    allL( "h0", hov"v:Tok", hov"y:list" )
    quasiprop
  }

  val app_assoc = hof"!x !y !z append( x, append( y, z )) = append( append( x, y ), z )"

  val lem = hof"!a !b !x !y ( append( lin(a), x ) = append( lin(b), y ) ->  ( a = b  & x = y ))"

  val lem_proof = Lemma( ( "app_assoc" -> app_assoc ) +: theory :+ ( "goal" -> lem ) ) {
    allR
    induction( hov"a:E" ) // outer case distinction

    //-- a starts with Plus
    allR
    induction( hov"b:E" ) // inner case distion

    //- a starts with Plus, b starts with Plus
    allR; allR; impR
    rewrite.many ltr "h6" in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many ltr ( "h4", "h5" ) in "goal_0"

    allL( "IHa_0", le"b_0:E" ).forget
    allL( "IHa_1", le"b_1:E" ).forget
    forget( "IHb_0", "IHb_1" )

    cut( "step_1", hof"append(lin(a_0), cons(Pl, append(lin(a_1), cons(D, x)))) = append(lin(b_0), cons(Pl, append(lin(b_1), cons(D, y))))" ); insert( cong_pos_proof )
    forget( "goal_0" )
    allL( "IHa_0", le"cons(Pl, append(lin(a_1), cons(D, x)))", le"cons(Pl, append(lin(b_1), cons(D, y)))" ).forget
    impL( "IHa_0" ); trivial
    andL( "IHa_0" )
    forget( "step_1" )

    cut( "step_2", hof"append(lin(a_1), cons(D, x)) = append(lin(b_1), cons(D, y))" ); insert( cong_pos_proof )
    forget( "IHa_0_1" )
    allL( "IHa_1", le"cons(D, x)", le"cons(D, y)" ).forget
    impL( "IHa_1" ); trivial
    andL( "IHa_1" )
    forget( "step_2" )

    cut( "step_3", hof"(x:list) = y" ); insert( cong_pos_proof )
    quasiprop

    //- a starts with Plus, b is EX
    allR; allR; impR
    rewrite.many ltr ( "h6", "h7" ) in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many ltr ( "h4", "h5" ) in "goal_0"
    insert( cong_neg_proof )

    //- a starts with Plus, b is EY
    allR; allR; impR
    rewrite.many ltr ( "h6", "h8" ) in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many ltr ( "h4", "h5" ) in "goal_0"
    insert( cong_neg_proof )

    //-- a is EX
    allR
    induction( hov"b:E" ) // inner case distion

    //- a is EX, b starts with Plus
    allR; allR; impR
    rewrite.many ltr ( "h6", "h7" ) in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many ltr ( "h4", "h5" ) in "goal_0"
    insert( cong_neg_symm_proof )

    //- a is EX, b is EX
    allR; allR; impR
    rewrite.many ltr ( "h4", "h5", "h7" ) in "goal_0"
    cut( "step_1", hof"(x:list) = y" ); insert( cong_pos_proof )
    quasiprop

    //- a is EX, b is EY
    allR; allR; impR
    rewrite.many ltr ( "h4", "h5", "h7", "h8" ) in "goal_0"
    insert( cong_neg_proof )

    //-- a is EY
    allR
    induction( hov"b:E" ) // inner case distion

    //- a is EY, b starts with Plus
    allR; allR; impR
    rewrite.many ltr ( "h6", "h8" ) in "goal_0"
    rewrite.many rtl "app_assoc" in "goal_0"
    rewrite.many ltr ( "h4", "h5" ) in "goal_0"
    insert( cong_neg_symm_proof )

    //- a is EY, b is EX
    allR; allR; impR
    rewrite.many ltr ( "h4", "h5", "h7", "h8" ) in "goal_0"
    insert( cong_neg_symm_proof )

    //- a is EY, b is EY
    allR; allR; impR
    rewrite.many ltr ( "h4", "h5", "h8" ) in "goal_0"
    cut( "step_1", hof"(x:list) = y" ); insert( cong_pos_proof )
    quasiprop
  }

  val proof = Lemma( ( "app_assoc" -> app_assoc ) +: sequent ) {
    allR; allR

    induction( hov"u:E" ) // outer case distinction

    //-- u starts with Plus
    induction( hov"v:E" ) // inner case distion

    //- u starts with Plus, v starts with Plus
    cut( "lem", lem ); insert( lem_proof ) // introduce lemma

    impR
    rewrite.many ltr ( "h6", "h5", "h4" ) in "goal_0"
    cut( "eq1", hof"append(append(append(lin(u_0), cons(Pl, nil)), lin(u_1)), cons(D, nil)) = append(append(append(lin(v_0), cons(Pl, nil)), lin(v_1)), cons(D, nil))" ); insert( cong_pos_proof )
    forget( "goal_0" )

    rewrite.many rtl "app_assoc" in "eq1"
    allL( "lem", hov"u_0:E", hov"v_0:E", // forward chaining would be useful here (FIXME?)
      le"append(cons(Pl, nil), append(lin(u_1), cons(D, nil)))",
      le"append(cons(Pl, nil), append(lin(v_1), cons(D, nil)))" )
    impL( "lem_0" ); trivial
    forget( "eq1" )

    andL( "lem_0" )
    rewrite.many ltr ( "h5", "h4" ) in "lem_0_1"
    cut( "eq2", hof"append(lin(u_1), cons(D, nil)) = append(lin(v_1), cons(D, nil))" ); insert( cong_pos_proof )

    allL( "lem", hov"u_1:E", hov"v_1:E", le"cons(D, nil)", le"cons(D, nil)" ) // forward chaining would be useful here (FIXME?)
    impL( "lem_1" ); trivial
    quasiprop

    //- u starts with Plus, v is EX
    impR
    rewrite.many ltr ( "h7", "h6" ) in "goal_0"
    rewrite.many rtl ( "app_assoc" ) in "goal_0"
    rewrite ltr "h5" in "goal_0"
    insert( cong_neg_proof )

    //- u starts with Plus, v is EY
    impR
    rewrite.many ltr ( "h8", "h6" ) in "goal_0"
    rewrite.many rtl ( "app_assoc" ) in "goal_0"
    rewrite ltr "h5" in "goal_0"
    insert( cong_neg_proof )

    //-- u is EX
    induction( hov"v:E" ) // inner case distion

    //- u is EX, v starts with Plus
    impR
    rewrite.many ltr ( "h7", "h6" ) in "goal_0"
    rewrite.many rtl ( "app_assoc" ) in "goal_0"
    rewrite ltr "h5" in "goal_0"
    insert( cong_neg_symm_proof )

    //- u is EX, v is EX
    quasiprop

    //- u is EX, v is EY
    impR
    rewrite.many ltr ( "h7", "h8" ) in "goal_0"
    insert( cong_neg_proof )

    //-- u is EY
    induction( hov"v:E" ) // inner case distion

    //- u is EY, v starts with Plus
    impR
    rewrite.many ltr ( "h8", "h6" ) in "goal_0"
    rewrite.many rtl ( "app_assoc" ) in "goal_0"
    rewrite ltr "h5" in "goal_0"
    insert( cong_neg_symm_proof )

    //- u is EY, v is EX
    impR
    rewrite.many ltr ( "h7", "h8" ) in "goal_0"
    insert( cong_neg_symm_proof )

    //- u is EY, v is EY
    quasiprop
  }
}
