package gapt.proofs.resolution

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.HOLAtomConst
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.logic.Polarity
import gapt.logic.hol.SkolemFunctions
import gapt.proofs._
import gapt.proofs.context.mutable.MutableContext
import gapt.utils.NameGenerator

import scala.collection.mutable

object structuralCNF {
  def apply(
    endSequent:        HOLSequent,
    propositional:     Boolean    = false,
    structural:        Boolean    = true,
    bidirectionalDefs: Boolean    = false,
    cse:               Boolean    = false )(
    implicit
    ctx: MutableContext = MutableContext.guess( endSequent ) ): Set[ResolutionProof] = {
    if ( !propositional )
      require( freeVariables( endSequent ).isEmpty, "end-sequent has free variables" )

    onProofs(
      endSequent.map( Sequent() :+ _, _ +: Sequent() ).map( Input ).elements,
      propositional, structural, bidirectionalDefs, cse )
  }

  def onProofs(
    proofs:            Iterable[ResolutionProof],
    propositional:     Boolean                   = false,
    structural:        Boolean                   = true,
    bidirectionalDefs: Boolean                   = false,
    cse:               Boolean                   = false )(
    implicit
    ctx: MutableContext = MutableContext.guess( proofs ) ): Set[ResolutionProof] = {
    val clausifier = new Clausifier( propositional, structural, bidirectionalDefs, cse, ctx, ctx.newNameGenerator )
    if ( cse ) proofs foreach clausifier.analyze
    proofs foreach clausifier.expand
    clausifier.cnf.toSet
  }
}

class Clausifier(
    propositional: Boolean, structural: Boolean,
    bidirectionalDefs: Boolean, cse: Boolean,
    ctx:     MutableContext,
    nameGen: NameGenerator ) {
  val cnf = mutable.Set[ResolutionProof]()
  val defs = mutable.Map[Expr, HOLAtomConst]()
  val skConsts = mutable.Map[Expr, Const]()

  def mkSkolemSym() = nameGen.freshWithIndex( "s" )
  def mkAbbrevSym() = nameGen.freshWithIndex( "D" )

  def getSkolemInfo( f: Formula, x: Var ): ( Expr, Expr ) = {
    val fvs = freeVariables( f ).toSeq
    val skolemizedFormula = Abs( fvs, f )
    val skolemConst = skConsts.getOrElseUpdate( skolemizedFormula, ctx.addSkolemSym( skolemizedFormula, mkSkolemSym() ) )
    ( skolemConst( fvs: _* ), skolemizedFormula )
  }

  val subExprs: mutable.Map[Expr, Int] = mutable.Map()
  val commonSubExprs: mutable.Set[Expr] = mutable.Set()
  def analyze( f: Formula ): Int = {
    subExprs.get( f ) match {
      case Some( compl ) =>
        if ( compl > 1 ) commonSubExprs += f
        compl
      case None =>
        val compl = f match {
          case _: Atom     => 1
          case Neg( a )    => analyze( a )
          case And( a, b ) => analyze( a ) + analyze( b )
          case Or( a, b )  => analyze( a ) + analyze( b )
          case Imp( a, b ) => analyze( a ) + analyze( b )
          case All( _, a ) => 1 + analyze( a )
          case Ex( _, a )  => 1 + analyze( a )
          case _           => 0
        }
        subExprs( f ) = compl
        compl
    }
  }
  def analyze( p: ResolutionProof ): Unit =
    p.conclusion.foreach( analyze )

  def isDefn( p: ResolutionProof ): Boolean = {
    def isDefnPlusAllR( p: ResolutionProof ): Boolean =
      p match {
        case Defn( _, _ )    => true
        case AllR( q, _, _ ) => isDefnPlusAllR( q )
        case _               => false
      }

    p match {
      case ImpR( AndR1( q, _ ), _ ) => isDefnPlusAllR( q )
      case ImpR( AndR2( q, _ ), _ ) => isDefnPlusAllR( q )
      case _                        => false
    }
  }

  // If we interpret the sequents in this set as a disjunction, their conjunction is equivalent to the original formula.

  // In each step we simplify the sequents in this set and make them more like clauses.

  // First we expand the connectives which correspond to nested disjunctions, e.g. (:- a|b) turns into (:- a, b).
  def expand( p: ResolutionProof ): Unit = {
    val p_Option = p.conclusion.zipWithIndex.elements.collectFirst {
      case ( f, i ) if cse && commonSubExprs.contains( f ) && !isDefn( p ) =>
        abbrev( p, i )

      case ( Ex( x, a ), i: Ant ) if !propositional =>
        ExL( p, i, rename( x, freeVariables( p.conclusion ) ) )
      case ( All( x, a ), i: Suc ) if !propositional =>
        AllR( p, i, rename( x, freeVariables( p.conclusion ) ) )
      case ( f @ All( x, a ), i: Ant ) if !propositional =>
        val ( skolemTerm, _ ) = getSkolemInfo( f, x )
        AllL( p, i, skolemTerm )
      case ( f @ Ex( x, a ), i: Suc ) if !propositional =>
        val ( skolemTerm, _ ) = getSkolemInfo( f, x )
        ExR( p, i, skolemTerm )

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

      case ( And( Bottom(), _ ), i: Suc ) => AndR1( p, i )
      case ( And( _, Bottom() ), i: Suc ) => AndR2( p, i )
      case ( Or( Top(), _ ), i: Ant )     => OrL1( p, i )
      case ( Or( _, Top() ), i: Ant )     => OrL2( p, i )
      case ( Imp( Bottom(), _ ), i: Ant ) => ImpL1( p, i )
      case ( Imp( _, Top() ), i: Ant )    => ImpL2( p, i )
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
        expand( abbrev( p, splits.head ) )
      case Seq( i, _* ) => splitAt( p, i )
      case Seq()        => cnf += p
    }
  }

  def splitAt( p: ResolutionProof, i: SequentIndex ): Unit =
    ( p.conclusion( i ), i ) match {
      case ( f, _ ) if cse && commonSubExprs( f ) && !isDefn( p ) => expand( p )
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
  def abbrev( p: ResolutionProof, i: SequentIndex ): DefIntro = {
    val f = p.conclusion( i )
    val fvs = freeVariables( f ).toList
    val definedFormula = Abs( fvs, f )
    val const = defs.getOrElseUpdate( definedFormula, ctx.addDefinition( definedFormula, mkAbbrevSym() ).asInstanceOf[HOLAtomConst] )
    expandDef( const, fvs, i.polarity )
    DefIntro( p, i, Definition( const, definedFormula ), fvs )
  }

  val alreadyDefined: mutable.Set[( Const, Polarity )] = mutable.Set()
  def expandDef( const: HOLAtomConst, fvs: List[Var], pol: Polarity ): Unit = {
    if ( alreadyDefined( const -> pol ) && ( !bidirectionalDefs || alreadyDefined( const -> !pol ) ) ) return
    val defn = fvs.foldLeft[ResolutionProof]( Defn( const, ctx.definition( const ).get ) )( AllR( _, Suc( 0 ), _ ) )
    if ( pol.inAnt || bidirectionalDefs ) {
      alreadyDefined += ( const -> Polarity.InAntecedent )
      expand( AndR2( defn, Suc( 0 ) ) )
    }
    if ( pol.inSuc || bidirectionalDefs ) {
      alreadyDefined += ( const -> Polarity.InSuccedent )
      expand( AndR1( defn, Suc( 0 ) ) )
    }
  }

}
