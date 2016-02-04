package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

object structuralCNF {
  def apply(
    endSequent:    HOLSequent,
    propositional: Boolean    = false, structural: Boolean = true
  ): Set[ResolutionProof] = {
    if ( !propositional )
      require( freeVariables( endSequent ).isEmpty, "end-sequent has free variables" )

    onProofs(
      endSequent.map( Sequent() :+ _, _ +: Sequent() ).map( Input( _ ) ).elements,
      propositional, structural
    )
  }

  def onProofs(
    proofs:        Iterable[ResolutionProof],
    propositional: Boolean                   = false,
    structural:    Boolean                   = true
  ): Set[ResolutionProof] = {
    val clausifier = new Clausifier( propositional, structural, rename.awayFrom( proofs.flatMap( containedNames( _ ) ) ) )
    proofs foreach clausifier.expand
    clausifier.cnf.toSet
  }
}

class Clausifier( propositional: Boolean, structural: Boolean, nameGen: NameGenerator ) {
  val cnf = mutable.Set[ResolutionProof]()
  val defs = mutable.Map[LambdaExpression, HOLAtomConst]()
  val skConsts = mutable.Map[LambdaExpression, Const]()

  def mkSkolemSym() = nameGen.freshWithIndex( "s" )
  def mkAbbrevSym() = nameGen.freshWithIndex( "D" )

  def getSkolemInfo( f: HOLFormula, x: Var ): ( LambdaExpression, LambdaExpression ) = {
    val fvs = freeVariables( f ).toSeq
    val skolemizedFormula = Abs( fvs, f )
    val skolemConst = skConsts.getOrElseUpdate(
      skolemizedFormula,
      Const( mkSkolemSym(), FunctionType( x.exptype, fvs map { _.exptype } ) )
    )
    ( skolemConst( fvs: _* ), skolemizedFormula )
  }

  // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.

  // In each step we simplify the sequents in this set and make them more like clauses.

  // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
  def expand( p: ResolutionProof ): Unit = {
    val p_Option = p.conclusion.zipWithIndex.elements.collectFirst {
      case ( Ex( x, a ), i: Ant ) if !propositional =>
        ExL( p, i, rename( x, freeVariables( p.conclusion ) ) )
      case ( All( x, a ), i: Suc ) if !propositional =>
        AllR( p, i, rename( x, freeVariables( p.conclusion ) ) )
      case ( f @ All( x, a ), i: Ant ) if !propositional =>
        val ( skolemTerm, skolemizedFormula ) = getSkolemInfo( f, x )
        AllL( p, i, skolemTerm, skolemizedFormula )
      case ( f @ Ex( x, a ), i: Suc ) if !propositional =>
        val ( skolemTerm, skolemizedFormula ) = getSkolemInfo( f, x )
        ExR( p, i, skolemTerm, skolemizedFormula )

      case ( Top(), i: Ant )              => TopL( p, i )
      case ( Bottom(), i: Suc )           => BottomR( p, i )
      case ( Top(), i: Suc )              => return
      case ( Bottom(), i: Ant )           => return

      case ( Neg( a ), i: Ant )           => NegL( p, i )
      case ( Neg( a ), i: Suc )           => NegR( p, i )

      case ( And( a, b ), i: Ant )        => AndL( p, i )
      case ( Imp( a, b ), i: Suc )        => ImpR( p, i )
      case ( Or( a, b ), i: Suc )         => OrR( p, i )

      case ( And( Top(), _ ), i: Suc )    => AndR2( p, i )
      case ( And( _, Top() ), i: Suc )    => AndR1( p, i )
      case ( Or( _, Bottom() ), i: Ant )  => OrL1( p, i )
      case ( Or( Bottom(), _ ), i: Ant )  => OrL2( p, i )
      case ( Imp( _, Bottom() ), i: Ant ) => ImpL1( p, i )
      case ( Imp( Top(), _ ), i: Ant )    => ImpL2( p, i )
      case ( And( Bottom(), _ ) | And( _, Bottom() ), i: Suc ) =>
        return
      case ( Or( Top(), _ ) | Or( _, Top() ) | Imp( Bottom(), _ ) | Imp( _, Top() ), i: Ant ) =>
        return
    }
    p_Option match {
      case Some( p_ ) => expand( p_ )
      case None =>
        if ( !p.conclusion.isTaut ) split( Factor( p ) )
    }
  }

  // Then we simplify the connectives which correspond to nested conjunctions, e.g. (:- a&b) turns into (:- a) and (:- b).
  // In order to combat exponential blow-up, we do something special if there are two or more such elements:
  // we introduce a definition for the first one.
  def split( p: ResolutionProof ): Unit = {
    p.conclusion.zipWithIndex.elements collect {
      case ( And( a, b ), i: Suc ) => i
      case ( Or( a, b ), i: Ant )  => i
      case ( Imp( a, b ), i: Ant ) => i
    } match {
      case splits if structural && ( splits.size > 1 || ( splits.size == 1 && p.conclusion.size > 3 ) ) =>
        abbrev( p, splits.head )
      case Seq( i, _* ) => splitAt( p, i )
      case Seq()        => cnf += p
    }
  }

  def splitAt( p: ResolutionProof, i: SequentIndex ): Unit =
    ( p.conclusion( i ), i ) match {
      case ( And( a, b ), i: Suc ) =>
        splitAt( AndR1( p, i ), p.conclusion.indices.last )
        splitAt( AndR2( p, i ), p.conclusion.indices.last )
      case ( Or( a, b ), i: Ant ) =>
        splitAt( OrL1( p, i ), Ant( 0 ) )
        splitAt( OrL2( p, i ), Ant( 0 ) )
      case ( Imp( a, b ), i: Ant ) =>
        splitAt( ImpL1( p, i ), Suc( p.conclusion.succedent.size ) )
        splitAt( ImpL2( p, i ), Ant( 0 ) )
      case _ => expand( p )
    }

  // Here, we replace the formula at index i with a definition, and continue with
  // both the abbreviated sequent, and (the necessary part of) the definition.
  def abbrev( p: ResolutionProof, i: SequentIndex ): Unit = {
    val f = p.conclusion( i )
    val fvs = if ( propositional ) Seq() else freeVariables( f ).toSeq
    val definition = Abs( fvs, f )
    val alreadyDefined = defs isDefinedAt definition
    val const = defs.getOrElseUpdate(
      Abs( fvs, f ),
      HOLAtomConst( mkAbbrevSym(), fvs map { _.exptype }: _* )
    )
    val repl = const( fvs: _* )
    if ( !alreadyDefined ) {
      expand( DefIntro( Taut( f ), if ( i isAnt ) Suc( 0 ) else Ant( 0 ), repl, definition ) )
    }
    expand( DefIntro( p, i, repl, definition ) )
  }

}
