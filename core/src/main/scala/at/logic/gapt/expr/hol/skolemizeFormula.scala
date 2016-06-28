package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

object skolemizeFormula {
  def apply( f: HOLFormula ): HOLFormula =
    new skolemizeFormula( rename.awayFrom( constants( f ) ) ).apply( f, true )

  def apply( sequent: HOLSequent ): HOLSequent = withDefs( sequent )._1

  def withDefs( sequent: HOLSequent ): ( HOLSequent, skolemizeFormula ) = {
    val skolemizer = new skolemizeFormula( rename.awayFrom( constants( sequent ) ) )
    val skSeq = for ( ( f, i ) <- sequent.zipWithIndex ) yield skolemizer( f, i.isSuc )
    ( skSeq, skolemizer )
  }
}

class skolemizeFormula( nameGenerator: NameGenerator ) {
  val skConsts = mutable.Map[LambdaExpression, Const]()

  private def skolemData( formula: HOLFormula ): ( LambdaExpression, LambdaExpression ) = {
    val Quant( v, _ ) = formula
    val fvs = freeVariables( formula ).toSeq
    val skDef = Abs( fvs, formula )
    val skConst = skConsts.getOrElseUpdate(
      skDef,
      Const( nameGenerator.freshWithIndex( "s" ), FunctionType( v.exptype, fvs.map( _.exptype ) ) )
    )
    val skTerm = skConst( fvs: _* )
    ( skDef, skTerm )
  }

  private def skolemizeQuant( formula: HOLFormula ): HOLFormula = instantiate( formula, skolemData( formula )._2 )

  def apply( formula: HOLFormula, pol: Boolean ): HOLFormula = formula match {
    case Top() | Bottom() | ( _: HOLAtom ) => formula
    case Neg( f )                          => -apply( f, !pol )
    case And( f, g )                       => apply( f, pol ) & apply( g, pol )
    case Or( f, g )                        => apply( f, pol ) | apply( g, pol )
    case Imp( f, g )                       => apply( f, !pol ) --> apply( g, pol )
    case All( v, f ) if pol                => apply( skolemizeQuant( formula ), pol )
    case Ex( v, f ) if !pol                => apply( skolemizeQuant( formula ), pol )
    case All( v, f ) if !pol               => All( v, apply( f, pol ) )
    case Ex( v, f ) if pol                 => Ex( v, apply( f, pol ) )
  }

  def addSkolemInfs( sh: HOLFormula, subst: Substitution, et: ExpansionTree ): ExpansionTree = ( sh, et ) match {
    case ( All( v, f ), _ ) if et.polarity =>
      val ( skDef, skTerm ) = skolemData( sh )
      val skTerm_ = subst( skTerm )
      val subst_ = subst compose Substitution( v -> skTerm )
      ETSkolemQuantifier( subst( sh ), skTerm_, skDef, addSkolemInfs( Substitution( v -> skTerm_ )( f ), subst_, et ) )
    case ( Ex( v, f ), _ ) if !et.polarity =>
      val ( skDef, skTerm ) = skolemData( sh )
      val skTerm_ = subst( skTerm )
      val subst_ = subst compose Substitution( v -> skTerm )
      ETSkolemQuantifier( subst( sh ), skTerm_, skDef, addSkolemInfs( Substitution( v -> skTerm_ )( f ), subst_, et ) )

    case ( _, ETWeakening( _, pol ) )                       => ETWeakening( subst( sh ), pol )

    case ( _, ETTop( _ ) | ETBottom( _ ) | ETAtom( _, _ ) ) => et

    case ( Neg( f ), ETNeg( a ) )                           => ETNeg( addSkolemInfs( f, subst, a ) )

    case ( And( f, g ), ETAnd( a, b ) )                     => ETAnd( addSkolemInfs( f, subst, a ), addSkolemInfs( g, subst, b ) )
    case ( Or( f, g ), ETOr( a, b ) )                       => ETOr( addSkolemInfs( f, subst, a ), addSkolemInfs( g, subst, b ) )
    case ( Imp( f, g ), ETImp( a, b ) )                     => ETImp( addSkolemInfs( f, subst, a ), addSkolemInfs( g, subst, b ) )

    case ( Quant( v, f ), ETWeakQuantifier( _, insts ) ) =>
      ETWeakQuantifier( subst( sh ), for ( ( t, i ) <- insts ) yield t -> addSkolemInfs( f, subst compose Substitution( v -> t ), i ) )

  }
}
