package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_32 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/prod/prop_32.smt2", getClass ) )
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

  val rot_gen = hof"!xs!ys!zs append(rotate(length(xs), append(xs,ys)), zs) = append(ys, append(xs, zs))"
  val rot_gen_proof = Lemma( theory :+
    ( "rot_gen" -> rot_gen ) ) {
    allR; induction( hov"xs:list" )
    //- BC
    allR; allR
    rewrite.many ltr "h3" in "rot_gen"
    rewrite.many ltr "h7" in "rot_gen"
    rewrite.many ltr "h5" in "rot_gen"; refl
    //- IC
    allR; allR
    rewrite.many ltr "h4" in "rot_gen"
    rewrite ltr "h6" in "rot_gen"
    rewrite.many ltr "h9" in "rot_gen"
    cut( "append_comm", hof"!xs!ys!zs append(xs,append(ys,zs)) = append(append(xs,ys),zs)" )
    insert( append_comm_proof )
    rewrite rtl "append_comm" in "rot_gen"
    rewrite.many ltr "IHxs_0" in "rot_gen"
    escargot
    /* FIXME: Is it possible to finish this proof without instantiating xs
     * in append_comm nor in any other derived formula to anything else than xs_0 and
     * without using induction on a variable other than xs?
     */
  }

  val proof = Lemma( sequent ) {
    cut( "rot_gen", rot_gen )
    insert( rot_gen_proof )
    cut( "append_nil_left_id", append_nil_left_id )
    insert( append_nil_left_id_proof )
    escargot
  }
}