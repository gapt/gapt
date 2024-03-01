package gapt.provers.simp

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.instantiate
import gapt.expr.subst.PreSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.util.LambdaPosition
import gapt.expr.util.LambdaPosition.Choice
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.replacementContext
import gapt.expr.util.syntacticMatching
import gapt.expr.util.toVNF
import gapt.expr.util.typeVariables
import gapt.logic.Polarity
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.expansion.ExpansionProofToLK
import gapt.proofs.expansion.formulaToExpansionTree
import gapt.proofs.gaptic.OpenAssumption
import gapt.proofs.gaptic.Tactic
import gapt.proofs.gaptic.TacticFailure
import gapt.proofs.gaptic.Tactical1
import gapt.proofs.lk._
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.BottomAxiom
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ParamodulationLeftRule
import gapt.proofs.lk.rules.macros.ParamodulationRightRule
import gapt.proofs.lk.rules.macros.WeakeningMacroRule
import gapt.provers.OneShotProver
import gapt.utils.Logger
import gapt.utils.Maybe

import scala.collection.mutable

sealed trait SimpIffResult {
  def proof: LKProof
  def lhs: Formula
  def rhs: Formula
  def pol: Polarity

  def >>( that: SimpIffResult ): SimpIffResult = {
    require( this.pol == that.pol )
    require( this.rhs == that.lhs )
    import SimpIffResult._
    ( this, that ) match {
      case ( Refl( _, _ ), _ ) => that
      case ( _, Refl( _, _ ) ) => this
      case ( Prf( p1, l1, m, _ ), Prf( p2, _, r2, _ ) ) =>
        Prf(
          ContractionMacroRule( if ( pol.inAnt ) CutRule( p1, p2, m ) else CutRule( p2, p1, m ) ),
          l1, r2, pol )
    }
  }

  def |( that: => SimpIffResult ): SimpIffResult =
    this match {
      case SimpIffResult.Refl( _, _ )      => that
      case SimpIffResult.Prf( _, _, _, _ ) => this
    }
}
object SimpIffResult {
  case class Refl( f: Formula, pol: Polarity ) extends SimpIffResult {
    def proof: LKProof = LogicalAxiom( f )
    def lhs: Formula = f
    def rhs: Formula = f
  }

  case class Prf( proof: LKProof, lhs: Formula, rhs: Formula, pol: Polarity ) extends SimpIffResult {
    val sequent =
      if ( pol.inAnt ) lhs +: Sequent() :+ rhs
      else rhs +: Sequent() :+ lhs
    require( sequent.isSubMultisetOf( proof.endSequent ) )
    override def toString = s"${lhs.toUntypedString} --> ${rhs.toUntypedString}: ${proof.endSequent.toString}"
  }
}

sealed trait SimpEqResult {
  def proof: LKProof
  def lhs: Expr
  def rhs: Expr
}
object SimpEqResult {
  case class Refl( f: Expr ) extends SimpEqResult {
    def proof: LKProof = ReflexivityAxiom( f )
    def lhs: Expr = f
    def rhs: Expr = f
  }

  case class Prf( proof: LKProof, lhs: Expr, rhs: Expr ) extends SimpEqResult {
    require( proof.endSequent.succedent.contains( lhs === rhs ) )
    override def toString = s"${lhs.toUntypedString} --> ${rhs.toUntypedString}: ${proof.endSequent.toString}"
  }
}

trait SimpProc {
  def freeVars: Set[Var] = Set()
  def simpIff( target: Formula, polarity: Polarity )( implicit simp: Simplifier ): SimpIffResult = SimpIffResult.Refl( target, polarity )
  def simpEq( target: Expr )( implicit simp: Simplifier ): SimpEqResult = SimpEqResult.Refl( target )
}

case class SimpLemmaProjection( proof: LKProof, conds: HOLSequent, idx: SequentIndex, fixed: PreSubstitution ) {
  val formula = proof.conclusion( idx )

  override def toString =
    formula.toUntypedString + ( if ( conds.isEmpty ) "" else s"  <--  ${conds.toNegConjunction.toUntypedString}" )

  def finishProof( p: LKProof, subst: Substitution )( implicit simp: Simplifier ): Option[LKProof] = {
    def procConds( p: LKProof, condInsts: Seq[( Formula, SequentIndex )] ): Option[LKProof] =
      condInsts match {
        case Seq() => Some( p )
        case ( c, Ant( _ ) ) +: cs =>
          simp.prove( c ) match {
            case None => None
            case Some( pc ) =>
              procConds( if ( !p.endSequent.antecedent.contains( c ) ) p
              else ContractionMacroRule( CutRule( pc, p, c ) ), cs )
          }
        case ( c, Suc( _ ) ) +: cs =>
          simp.refute( c ) match {
            case None => None
            case Some( pc ) =>
              procConds( if ( !p.endSequent.succedent.contains( c ) ) p
              else ContractionMacroRule( CutRule( p, pc, c ) ), cs )
          }
      }
    procConds( ContractionMacroRule( p ), subst( conds ).zipWithIndex.elements )
  }

  def finishProof( res: SimpIffResult, subst: Substitution )( implicit simp: Simplifier ): SimpIffResult =
    res match {
      case SimpIffResult.Refl( _, _ ) => res
      case res @ SimpIffResult.Prf( p, lhs, _, pol ) =>
        finishProof( p, subst ) match {
          case None       => SimpIffResult.Refl( lhs, pol )
          case Some( p_ ) => res.copy( proof = p_ )
        }
    }
  def finishProof( res: SimpEqResult, subst: Substitution )( implicit simp: Simplifier ): SimpEqResult =
    res match {
      case SimpEqResult.Refl( _ ) => res
      case res @ SimpEqResult.Prf( p, lhs, _ ) =>
        finishProof( p, subst ) match {
          case None       => SimpEqResult.Refl( lhs )
          case Some( p_ ) => res.copy( proof = p_ )
        }
    }
}

case class NegAtomSimpLemma( proj: SimpLemmaProjection ) extends SimpProc {
  override def freeVars = proj.fixed.domain
  require( proj.idx.isAnt )
  override def simpIff( target: Formula, polarity: Polarity )( implicit simp: Simplifier ): SimpIffResult =
    syntacticMatching( proj.formula, target, proj.fixed ) match {
      case None => SimpIffResult.Refl( target, polarity )
      case Some( subst ) =>
        if ( polarity.inAnt ) {
          // target :- Bottom()
          val p = WeakeningRightRule( subst( proj.proof ), Bottom() )
          proj.finishProof( SimpIffResult.Prf( p, target, Bottom(), polarity ), subst )
        } else {
          // Bottom() :- target
          val p = WeakeningRightRule( BottomAxiom, target )
          proj.finishProof( SimpIffResult.Prf( p, target, Bottom(), polarity ), subst )
        }
    }
}

case class AtomSimpLemma( proj: SimpLemmaProjection ) extends SimpProc {
  override def freeVars = proj.fixed.domain
  require( proj.idx.isSuc )
  override def simpIff( target: Formula, polarity: Polarity )( implicit simp: Simplifier ): SimpIffResult =
    syntacticMatching( proj.formula, target, proj.fixed ) match {
      case None => SimpIffResult.Refl( target, polarity )
      case Some( subst ) =>
        if ( polarity.inAnt ) {
          // target :- Top()
          val p = WeakeningLeftRule( TopAxiom, target )
          proj.finishProof( SimpIffResult.Prf( p, target, Top(), polarity ), subst )
        } else {
          // Top() :- target
          val p = WeakeningLeftRule( subst( proj.proof ), Top() )
          proj.finishProof( SimpIffResult.Prf( p, target, Top(), polarity ), subst )
        }
    }
}

case class IffSimpLemma( proj: SimpLemmaProjection ) extends SimpProc {
  override def freeVars = proj.fixed.domain
  require( proj.idx.isSuc )
  val Iff( lhs, rhs ) = proj.formula: @unchecked

  val lk1 = SimpLemmas.project( SimpLemmas.project( proj, j = 1 ) ).proof
  val lk2 = SimpLemmas.project( SimpLemmas.project( proj, j = 2 ) ).proof

  override def simpIff( target: Formula, polarity: Polarity )( implicit simp: Simplifier ): SimpIffResult =
    syntacticMatching( lhs, target, proj.fixed ) match {
      case None => SimpIffResult.Refl( target, polarity )
      case Some( subst ) =>
        val p = subst( if ( polarity.inAnt ) lk1 else lk2 )
        proj.finishProof( SimpIffResult.Prf( p, target, subst( rhs ), polarity ), subst )
    }
}

case class EqSimpLemma( proj: SimpLemmaProjection ) extends SimpProc {
  override def freeVars = proj.fixed.domain
  require( proj.idx.isSuc )
  val Eq( lhs, rhs ) = proj.formula: @unchecked

  override def simpEq( target: Expr )( implicit simp: Simplifier ): SimpEqResult =
    syntacticMatching( lhs, target, proj.fixed ) match {
      case None => SimpEqResult.Refl( target )
      case Some( subst ) =>
        proj.finishProof( SimpEqResult.Prf( subst( proj.proof ), target, subst( rhs ) ), subst )
    }
}

case object QPropSimpProc extends SimpProc {
  def simplifyHere( f: Formula ): Formula =
    f match {
      case Eq( t, t_ ) if t == t_ => Top()
      case And( Top(), a ) => simplifyHere( a )
      case And( a, Top() ) => simplifyHere( a )
      case And( Bottom(), _ ) | And( _, Bottom() ) => Bottom()
      case Or( a, Bottom() ) => simplifyHere( a )
      case Or( Bottom(), a ) => simplifyHere( a )
      case Or( Top(), _ ) | Or( _, Top() ) => Top()
      case Or( a, Neg( b ) ) if a == b => Top()
      case Imp( a, Bottom() ) => Neg( a )
      case Imp( Top(), a ) => simplifyHere( a )
      case Imp( _, Top() ) | Imp( Bottom(), _ ) => Top()
      case Imp( a, a_ ) if a == a_ => Top()
      case Neg( Top() ) => Bottom()
      case Neg( Bottom() ) => Top()
      case Neg( Neg( a ) ) => a
      case Neg( And( a, b ) ) => -a | -b
      case Neg( Or( a, b ) ) => -a & -b
      case Neg( Imp( a, b ) ) => a & -b
      case Quant( x, sub, _ ) if !freeVariables( sub ).contains( x ) => simplifyHere( sub )
      case Neg( Quant( x, sub, pol ) ) => simplifyHere( Quant( x, -sub, !pol ) )
      case _ => f
    }

  override def simpIff( f0: Formula, polarity: Polarity )( implicit simp: Simplifier ): SimpIffResult = {
    val f = toVNF( f0 )
    val g = simplifyHere( f )
    if ( f == g ) SimpIffResult.Refl( f, polarity ) else {
      val sequent = if ( polarity.inAnt ) f +: Sequent() :+ g else g +: Sequent() :+ f
      val expansion = for ( ( a, i ) <- sequent.zipWithIndex ) yield formulaToExpansionTree( a, Set( Substitution() ), i.polarity )
      val Right( lk ) = new ExpansionProofToLK( cl =>
        cl.succedent.collectFirst { case Eq( s, t ) if s == t => ReflexivityAxiom( t ) } )( ExpansionProof( expansion ) ): @unchecked
      SimpIffResult.Prf( lk, f, g, polarity )
    }
  }
}

case class Simplifier( lemmas: Seq[SimpProc] ) {
  private val freeVars = lemmas.view.flatMap( _.freeVars ).toSet
  private implicit def simplifier: Simplifier = this

  def simpIff( f: Formula, pol: Polarity ): SimpIffResult = {
    val ress =
      lemmas.view.map( _.simpIff( f, pol ) ).
        find( !_.isInstanceOf[SimpIffResult.Refl] ).
        getOrElse( simpEq( f, pol ) | congrIff( f, pol ) ) match {
          case res @ SimpIffResult.Prf( p, _, g, _ ) =>
            require( f == res.lhs )
            require( res.pol == pol )
            res >> simpIff( g, pol )
          case res @ SimpIffResult.Refl( _, _ ) =>
            require( f == res.lhs )
            require( res.pol == pol )
            res
        }
    require( ress.lhs == f )
    require( ress.pol == pol )
    Simplifier.logger.info( s"${ress.lhs.toUntypedString} --> ${ress.rhs.toUntypedString}" )
    ress
  }

  def congrIff( f: Formula, pol: Polarity ): SimpIffResult = {
    def congr1( res: SimpIffResult, frm: Formula => Formula, prf: ( Formula, Formula, LKProof ) => LKProof ): SimpIffResult =
      res match {
        case SimpIffResult.Refl( _, _ ) => SimpIffResult.Refl( f, pol )
        case SimpIffResult.Prf( p, _, a_, _ ) =>
          val ( l, r ) = if ( res.pol.inAnt ) ( res.lhs, res.rhs ) else ( res.rhs, res.lhs )
          SimpIffResult.Prf( ContractionMacroRule( prf( l, r, p ) ), f, frm( a_ ), pol )
      }
    def congr2( res1: SimpIffResult, res2: SimpIffResult, frm: ( Formula, Formula ) => Formula,
                prf: ( Formula, Formula, LKProof, Formula, Formula, LKProof ) => LKProof ): SimpIffResult =
      ( res1, res2 ) match {
        case ( SimpIffResult.Refl( _, _ ), SimpIffResult.Refl( _, _ ) ) => SimpIffResult.Refl( f, pol )
        case ( _, _ ) =>
          val ( l1, r1 ) = if ( res1.pol.inAnt ) ( res1.lhs, res1.rhs ) else ( res1.rhs, res1.lhs )
          val ( l2, r2 ) = if ( res2.pol.inAnt ) ( res2.lhs, res2.rhs ) else ( res2.rhs, res2.lhs )
          SimpIffResult.Prf(
            ContractionMacroRule( prf( l1, r1, res1.proof, l2, r2, res2.proof ) ),
            f, frm( res1.rhs, res2.rhs ), pol )
      }
    val res = f match {
      case Neg( a ) =>
        congr1( simpIff( a, !pol ), Neg( _ ), ( l, r, p ) => NegRightRule( NegLeftRule( p, r ), l ) )
      case And( a, b ) =>
        congr2( simpIff( a, pol ), simpIff( b, pol ), And( _, _ ),
          ( l1, r1, p1, l2, r2, p2 ) => AndLeftRule( AndRightRule( p1, p2, r1 & r2 ), l1 & l2 ) )
      case Or( a, b ) =>
        congr2( simpIff( a, pol ), simpIff( b, pol ), Or( _, _ ),
          ( l1, r1, p1, l2, r2, p2 ) => OrRightRule( OrLeftRule( p1, p2, l1 | l2 ), r1 | r2 ) )
      case Imp( a, b ) =>
        congr2( simpIff( a, !pol ), simpIff( b, pol ), Imp( _, _ ),
          ( l1, r1, p1, l2, r2, p2 ) => ImpRightRule( ImpLeftRule( p1, p2, r1 --> l2 ), l1 --> r2 ) )
      case Quant( x, _, p ) if freeVars.contains( x ) || freeVariables( f ).contains( x ) =>
        val y = rename( x, freeVars ++ freeVariables( f ) )
        congrIff( Quant( y, instantiate( f, y ), p ), pol )
      case All( x, a ) =>
        congr1( simpIff( a, pol ), All( x, _ ),
          ( l, r, p ) => ForallRightRule( ForallLeftRule( p, All( x, l ), x ), All( x, r ), x ) )
      case Ex( x, a ) =>
        congr1( simpIff( a, pol ), Ex( x, _ ),
          ( l, r, p ) => ExistsLeftRule( ExistsRightRule( p, Ex( x, r ), x ), Ex( x, l ), x ) )
      case _ => SimpIffResult.Refl( f, pol )
    }
    require( res.lhs == f )
    require( res.pol == pol )
    res
  }

  def getLambdaPositions( exp: Expr ): Map[Expr, Seq[LambdaPosition]] = {
    val poss = mutable.Map[Expr, Seq[LambdaPosition]]().withDefaultValue( Seq() )
    def walk( exp: Expr, pos: List[Choice] ): Unit = {
      poss( exp ) :+= LambdaPosition( pos.reverse: _* )
      exp match {
        case App( a, b ) =>
          walk( a, LambdaPosition.Left :: pos )
          walk( b, LambdaPosition.Right :: pos )
        case _ =>
      }
    }
    walk( exp, Nil )
    poss.toMap
  }

  def simpEq( formula: Formula, pol: Polarity ): SimpIffResult =
    formula match { case a: Atom => simpEq( a, pol ) case _ => SimpIffResult.Refl( formula, pol ) }
  def simpEq( f0: Atom, pol: Polarity ): SimpIffResult = {
    var p: LKProof = LogicalAxiom( f0 )
    var f = f0
    var didRewrite = true
    while ( didRewrite ) {
      didRewrite = false
      for {
        ( subterm, pos ) <- getLambdaPositions( f ) if !didRewrite
        lem <- lemmas if !didRewrite
        case SimpEqResult.Prf( lemP, _, subterm_ ) <- Some( lem.simpEq( subterm ) ) if !didRewrite
        ctx = replacementContext( subterm_.ty, f, pos )
      } {
        p = ContractionMacroRule(
          if ( pol.inSuc ) ParamodulationLeftRule( lemP, subterm === subterm_, p, f, ctx )
          else ParamodulationRightRule( lemP, subterm === subterm_, p, f, ctx ) )
        f = Substitution( ctx.variable -> subterm_ )( ctx.term ).asInstanceOf[Atom]
        didRewrite = true
      }
    }
    if ( f == f0 ) SimpIffResult.Refl( f0, pol )
    else SimpIffResult.Prf( p, f0, f, pol )
  }

  def simpEqToEql( t0: Expr ): SimpEqResult = {
    var p: LKProof = ReflexivityAxiom( t0 )
    var t = t0
    var didRewrite = true
    while ( didRewrite ) {
      didRewrite = false
      for {
        ( subterm, pos ) <- getLambdaPositions( t ) if !didRewrite
        lem <- lemmas if !didRewrite
        case SimpEqResult.Prf( lemP, _, subterm_ ) <- Some( lem.simpEq( subterm ) ) if !didRewrite
        ctx = replacementContext( subterm_.ty, t0 === t, pos.map( LambdaPosition.Right :: _ ) )
      } {
        p = ContractionMacroRule(
          ParamodulationRightRule( lemP, subterm === subterm_, p, t0 === t, ctx ) )
        t = Substitution( ctx.variable -> subterm_ )( ctx.term( LambdaPosition( LambdaPosition.Right ) ) )
        didRewrite = true
      }
    }
    if ( t == t0 ) SimpEqResult.Refl( t0 )
    else SimpEqResult.Prf( p, t0, t )
  }

  def prove( f: Formula ): Option[LKProof] = {
    val res = simpIff( f, Polarity.InSuccedent )
    res.rhs match {
      case Top() => Some( CutRule( TopAxiom, res.proof, Top() ) )
      case _     => None
    }
  }

  def refute( f: Formula ): Option[LKProof] = {
    val res = simpIff( f, Polarity.InAntecedent )
    res.rhs match {
      case Bottom() => Some( CutRule( res.proof, BottomAxiom, Bottom() ) )
      case _        => None
    }
  }
}
object Simplifier {
  val logger = Logger( "simp" )
}

object SimpProver extends OneShotProver {
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
    val simpLemmas = SimpLemmas.collect( seq.antecedent ++: Sequent() )
    val simp = Simplifier( simpLemmas.toSeq )
    seq.succedent.view.flatMap( simp.prove ).headOption
  }
}

object SimpLemmas {
  private[simp] def project( proj: SimpLemmaProjection, j: Int = 0, x: Var = FOLVar( "x" ) ): SimpLemmaProjection = {
    val ( newProof, conn ) = new LKVisitor[Option[SequentIndex]] {
      override def transportToSubProof( arg: Option[SequentIndex], proof: LKProof, subProofIdx: Int ): Option[SequentIndex] =
        arg.flatMap( proof.occConnectors( subProofIdx ).parentOption( _ ) )
      override def visitLogicalAxiom( proof: LogicalAxiom, idx: Option[SequentIndex] ): ( LKProof, SequentConnector ) =
        if ( idx.isEmpty ) super.visitLogicalAxiom( proof, idx ) else
          ( ( proof.conclusion( idx.get ), idx.get, j ): @unchecked ) match {
            case ( f @ And( a, b ), Suc( _ ), 1 ) =>
              AndLeftRule( WeakeningLeftRule( LogicalAxiom( a ), b ), f ) -> SequentConnector( proof.conclusion )
            case ( f @ And( a, b ), Suc( _ ), 2 ) =>
              AndLeftRule( WeakeningLeftRule( LogicalAxiom( b ), a ), f ) -> SequentConnector( proof.conclusion )
            case ( f @ All( _, _ ), Suc( _ ), _ ) =>
              ForallLeftRule( LogicalAxiom( instantiate( f, x ) ), f, x ) -> SequentConnector( proof.conclusion )
            case ( Neg( a ), Suc( _ ), _ ) =>
              NegLeftRule( LogicalAxiom( a ), a ) ->
                SequentConnector( ( 2, 0 ), ( 1, 1 ), Seq( Ant( 0 ) ) +: Seq( Suc( 0 ) ) +: Sequent() )
            case ( Neg( a ), Ant( _ ), _ ) =>
              NegRightRule( LogicalAxiom( a ), a ) ->
                SequentConnector( ( 0, 2 ), ( 1, 1 ), Sequent() :+ Seq( Ant( 0 ) ) :+ Seq( Suc( 0 ) ) )
            case ( f @ Imp( a, b ), Suc( _ ), _ ) =>
              ImpLeftRule( LogicalAxiom( a ), LogicalAxiom( b ), f ) ->
                SequentConnector( ( 2, 1 ), ( 1, 1 ), Seq( Ant( 0 ) ) +: Seq() +: Sequent() :+ Seq( Suc( 0 ) ) )
          }
    }.withSequentConnector( proj.proof, Some( proj.idx ) )
    proj.copy( proof = newProof, idx = conn.child( proj.idx ) )
  }

  def collect( proj: SimpLemmaProjection ): Set[SimpProc] = {
    def containsAllVars( e: Expr ): Boolean =
      freeVariables( proj.proof.conclusion ).diff( proj.fixed.domain ).subsetOf( freeVariables( e ) )
    ( proj.formula, proj.idx ) match {
      case ( Iff( lhs, _ ), Suc( _ ) ) if containsAllVars( lhs ) =>
        Set( IffSimpLemma( proj ) )
      case ( Eq( lhs, _ ), Suc( _ ) ) if containsAllVars( lhs ) =>
        Set( EqSimpLemma( proj ) )
      case ( f: Atom, Suc( _ ) ) if containsAllVars( f ) => Set( AtomSimpLemma( proj ) )
      case ( f: Atom, Ant( _ ) ) if containsAllVars( f ) => Set( NegAtomSimpLemma( proj ) )
      case ( Imp( lhs, rhs ), Suc( _ ) ) if containsAllVars( rhs ) =>
        val proj_ = project( proj )
        collect( proj_.copy( conds = lhs +: proj_.conds ) )
      case ( And( _, _ ), Suc( _ ) ) =>
        collect( project( proj, 1 ) ) ++ collect( project( proj, 2 ) )
      //      case ( Or( _, _ ), Ant( _ ) )  => c( OrL1( p, i ) ) ++ c( OrL2( p, i ) )
      case ( Neg( _ ), _ ) => collect( project( proj ) )
      case ( f @ All( x0, _ ), Suc( _ ) ) =>
        val x = rename( x0, freeVariables( f ) ++ proj.fixed.domain )
        collect( project( proj, x = x ) )
      //      case ( f @ Ex( x0, _ ), Ant( _ ) ) =>
      //        val x = rename( x0, freeVariables( f ) ++ fixed.domain )
      //        c( ExL( p, i, x ) )
      case _ => Set()
    }
  }

  def collectFromLemma( f: Formula ): Set[SimpProc] =
    collect( SimpLemmaProjection( LogicalAxiom( f ), Sequent(), Suc( 0 ), PreSubstitution() ) )

  def collectFromLemma( n: String )( implicit ctx: Context ): Set[SimpProc] =
    collectFromProofName( ctx.get[ProofNames].names( n )._1 )

  def collectFromProofName( proofName: Expr )( implicit ctx: Context ): Set[SimpProc] = {
    val link = ProofLink( proofName )
    val formula = link.conclusion.succedent.head
    collect( SimpLemmaProjection( CutRule( link, LogicalAxiom( formula ), formula ), Sequent(), Suc( 0 ), PreSubstitution() ) )
  }

  def collectFromAnt( seq: HOLSequent ): Set[SimpProc] =
    collect( Sequent( seq.antecedent, Seq() ) )

  def collect( seq: HOLSequent ): Set[SimpProc] = {
    val fixed = new PreSubstitution(
      Map() ++ freeVariables( seq ).map( v => v -> v ),
      Map() ++ typeVariables( seq.toImplication ).map( v => v -> v ) )
    Set() ++ seq.zipWithIndex.elements.flatMap {
      case ( f, i ) =>
        collect( SimpLemmaProjection( LogicalAxiom( f ), Sequent(), if ( i.isAnt ) Suc( 0 ) else Ant( 0 ), fixed ) )
    }
  }
}

case class SimpTactic(
    onLabel:            Option[String] = None,
    extraLemmasList:    Seq[String]    = Seq(),
    excludedLemmasList: Set[String]    = Set(),
    useAssumptions:     Boolean        = false )( implicit ctx: Context ) extends Tactical1[Unit] {
  def h = copy( useAssumptions = true )
  def on( label: String ) = copy( onLabel = Some( label ) )
  def apply( lemmas: String* ) = copy( extraLemmasList = extraLemmasList ++ lemmas )
  def w( lemmas: String* ) = apply( lemmas: _* )
  def wo( lemmas: String* ) = copy( excludedLemmasList = excludedLemmasList ++ lemmas )

  private def mkSimpLemmas( goal: OpenAssumption ): Seq[SimpProc] = {
    var sls: Seq[SimpProc] = Seq( QPropSimpProc )
    sls ++= ctx.get[Attributes].lemmasWith( "simp" ).
      filterNot( excludedLemmasList ).
      flatMap( SimpLemmas.collectFromLemma )
    sls ++= SimpLemmas.collect( goal.labelledSequent.filter {
      case ( l, _ ) =>
        !onLabel.contains( l ) && !excludedLemmasList( l ) &&
          ( useAssumptions || extraLemmasList.contains( l ) )
    }.map( _._2 ) )
    val goalLabels = goal.labelledSequent.map( _._1 ).elements.toSet
    for ( l <- extraLemmasList if !goalLabels.contains( l ) )
      sls ++= SimpLemmas.collectFromLemma( l )
    Simplifier.logger.info( "simp lemmas:\n" + sls.mkString( "\n" ) )
    sls
  }

  override def apply( goal: OpenAssumption ): Tactic[Unit] =
    onLabel match {
      case None =>
        if ( goal.conclusion.succedent.isEmpty ) TacticFailure( this, "no formula in succedent" )
        else copy( onLabel = Some( goal.labelledSequent.succedent.head._1 ) ).apply( goal )
      case Some( target ) if goal.labelledSequent.exists( _._1 == target ) =>
        val Some( target ) = onLabel: @unchecked
        val Some( idx ) = goal.labelledSequent.find( _._1 == target ): @unchecked
        val formula = goal.conclusion( idx )
        val simp = Simplifier( mkSimpLemmas( goal ) )
        val res = simp.simpIff( formula, idx.polarity )
        val newSeq = goal.labelledSequent.updated( idx, target -> res.rhs )
        val newSeqF = newSeq.map( _._2 )
        val newSeqProof =
          WeakeningMacroRule(
            if ( newSeqF.isTaut )
              LogicalAxiom( newSeqF.antecedent.intersect( newSeqF.succedent ).head )
            else if ( newSeqF.antecedent.contains( Bottom() ) )
              BottomAxiom
            else if ( newSeqF.succedent.contains( Top() ) )
              TopAxiom
            else
              newSeqF.succedent.collectFirst {
                case Eq( t, t_ ) if t == t_ => ReflexivityAxiom( t )
              }.getOrElse( OpenAssumption( newSeq ) ), newSeqF )
        replace( ContractionMacroRule( if ( idx.isAnt )
          CutRule( res.proof, newSeqProof, res.rhs )
        else
          CutRule( newSeqProof, res.proof, res.rhs ) ) )
      case Some( target ) => TacticFailure( this, s"label $target not found" )
    }
}