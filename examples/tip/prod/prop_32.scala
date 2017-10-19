package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_32 extends TacticsProof {

  val bench = def_prop_32.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }
  val theory = sequent.antecedent ++: Sequent()

  val append_nil_left_id = hof"!xs append(xs,nil) = xs"
  val append_nil_left_id_proof = Lemma( theory :+
    ( "append_nil_left_id" -> append_nil_left_id ) ) {
    allR; induction( hov"xs:list" )
    //- BC
    rewrite.many ltr "h5" in "append_nil_left_id"; refl
    //- IC
    rewrite.many ltr "h6" in "append_nil_left_id";
    rewrite.many ltr "IHxs_0" in "append_nil_left_id"; refl
  }

  val append_comm = hof"!xs!ys!zs append(xs,append(ys,zs)) = append(append(xs,ys),zs)"
  val append_comm_proof = Lemma( theory :+
    ( "append_comm" -> append_comm ) ) {
    allR; induction( hov"xs:list" )
    //- BC
    allR; allR;
    rewrite.many ltr "h5" in "append_comm"; refl
    //- IC
    allR; allR;
    rewrite.many ltr "h6" in "append_comm"
    rewrite.many ltr "IHxs_0" in "append_comm"; refl
  }

  val rot_gen = ( append_nil_left_id & append_comm ) -->
    hof"!xs!ys rotate(length(xs), append(xs,ys)) = append(ys, xs)"

  val rot_gen_proof = Lemma( theory :+ ( "rot_gen" -> rot_gen ) ) {
    impR; andL; allR; induction( hov"xs:list" )
    //- BC
    escargot
    //- IC
    allR
    rewrite.many ltr "h4" in "rot_gen_1"
    rewrite.many ltr "h6" in "rot_gen_1"
    escargot
  }

  val lemma = append_nil_left_id & append_comm & rot_gen

  val lemma_proof = Lemma( theory :+ ( "lemma" -> lemma ) ) {
    andR; andR;
    insert( append_nil_left_id_proof )
    insert( append_comm_proof )
    insert( rot_gen_proof )
  }

  val proof = Lemma( sequent ) {
    cut( "lemma", lemma )
    insert( lemma_proof )
    escargot
  }
}