package gapt.proofs.lk

import gapt.expr._
import gapt.expr.hol.{ containsQuantifierOnLogicalLevel, instantiate }
import gapt.grammars.InductionGrammar
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.expansion._
import gapt.proofs.lk.transformations.LKToExpansionProof

object extractInductionGrammar {

  def apply( p: LKProof )( implicit ctx: Context ): InductionGrammar =
    apply( p, InstanceTermEncoding( p.endSequent ) )

  def apply( p: LKProof, encoding: InstanceTermEncoding )( implicit ctx: Context ): InductionGrammar =
    apply( LKToExpansionProof( p ), encoding )

  def apply( p: ExpansionProof )( implicit ctx: Context ): InductionGrammar =
    apply( p, InstanceTermEncoding( p.nonTheoryPart.shallow ) )

  def apply( p: ExpansionProof, encoding: InstanceTermEncoding )( implicit ctx: Context ): InductionGrammar = {
    if ( !p.isCutFree ) return apply( eliminateCutsET( p ), encoding )
    if ( freeVariablesET( p ).nonEmpty ) // ground proof
      return apply( Substitution( freeVariablesET( p ).map( v => v ->
        ctx.getConstructors( v.ty ).toVector.flatten.
        find( _.ty == v.ty ).
        getOrElse( Const( "dummy", v.ty ) ) ) )( p ), encoding )
    require( p.inductions.length == 1, s"Number of inductions not equal to 1: ${p.inductions.length}" )
    val Vector( ind ) = p.inductions
    val nus = ind.constructorsSteps.map( c => c.constr -> c.evs.toList ).toMap
    val nameGen = rename.awayFrom( nus.values.flatten )
    val All( _, indFormula @ All.Block( gamma0, indFormulaMatrix ) ) = ind.suc.shallow
    require(
      !containsQuantifierOnLogicalLevel( indFormulaMatrix ),
      s"induction formula is not purely universal:\n$indFormula" )
    val gamma = gamma0.map( nameGen.fresh( _ ) )
    val subst = Substitution( ind.constructorsSteps.flatMap { c =>
      val ETStrongQuantifierBlock( _, gammaC, _ ) = c.auxiliary.succedent.head
      gammaC zip gamma
    } )
    require( p.expansionSequent.succedent.size == 1, s"Not exactly 1 expansion tree in succedent" )
    val Seq( ETStrongQuantifier( _, alpha, _ ) ) = p.expansionSequent.succedent
    val goal = p.expansionSequent.succedent.head.shallow
    require(
      !containsQuantifierOnLogicalLevel( instantiate( goal, alpha ) ),
      s"goal does not have exactly 1 quantifier:\n$goal" )
    require(
      ctx.getConstructors( alpha.ty ).isDefined,
      s"quantifier $alpha in goal is not over a structurally inductive type:\n$goal" )
    val gammaProds2 = ind.suc match {
      case ETWeakQuantifierBlock( _, _, insts ) =>
        for ( ( inst, _ ) <- insts )
          yield InductionGrammar.Production( gamma, subst( inst.tail.toList ) )
    }
    val tau = nameGen.fresh( Var( "τ", encoding.instanceTermType ) )
    val tauProds = encoding.encode( p.nonTheoryPart.antecedent ++: Sequent() ).
      map( t => InductionGrammar.Production( tau, subst( t ) ) ).toVector
    val gammaProds1 =
      for {
        c <- ind.constructorsSteps
        ETWeakQuantifierBlock( _, _, insts ) <- c.auxiliary.antecedent
        ( inst, _ ) <- insts
      } yield InductionGrammar.Production( gamma, subst( inst ).toList )
    InductionGrammar( tau, alpha, nus, gamma, tauProds ++ gammaProds1 ++ gammaProds2 )
  }

}
