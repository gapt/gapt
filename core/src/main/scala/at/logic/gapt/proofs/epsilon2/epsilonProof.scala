package at.logic.gapt.proofs.epsilon2

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ SkolemFunctions, instantiate }
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature }
import at.logic.gapt.proofs.epsilon.EpsilonC
import at.logic.gapt.proofs.{ Checkable, Context, HOLSequent, MutableContext }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.{ LKProof, LKToExpansionProof }
import at.logic.gapt.utils.Doc

import scala.collection.mutable

case class CriticalFormula( skTerm: Expr, term: Expr ) {
  val Apps( skSym: Const, skArgs ) = skTerm
  def deep( implicit ctx: Context ): Formula = {
    val Some( Abs.Block( vs, Quant( x, qfFormula, pol ) ) ) = ctx.skolemDef( skSym )
    val formulaWithSk: Formula = Substitution( ( vs zip skArgs ) :+ ( x -> skTerm ) )( qfFormula )
    val formulaWithTerm: Formula = Substitution( ( vs zip skArgs ) :+ ( x -> term ) )( qfFormula )
    if ( pol ) formulaWithSk --> formulaWithTerm else formulaWithTerm --> formulaWithSk
  }

  def toSigRelativeString( implicit sig: BabelSignature ): String = {
    val exporter = new BabelExporter( unicode = true, sig = sig )
    import exporter._
    nest( show( skTerm ) <+> "→" </> show( term ) ).render( lineWidth )
  }
  override def toString: String = toSigRelativeString
}

object CriticalFormula {
  implicit def ofPair( pair: ( Expr, Expr ) ): CriticalFormula =
    CriticalFormula( pair._1, pair._2 )

  implicit object closedUnderSubstitution extends ClosedUnderSub[CriticalFormula] {
    override def applySubstitution( sub: Substitution, arg: CriticalFormula ): CriticalFormula =
      CriticalFormula( sub( arg.skTerm ), sub( arg.term ) )
  }
  implicit object closedUnderReplacement extends ClosedUnderReplacement[CriticalFormula] {
    override def replace( obj: CriticalFormula, p: PartialFunction[Expr, Expr] ): CriticalFormula =
      CriticalFormula( TermReplacement( obj.skTerm, p ), TermReplacement( obj.term, p ) )

    override def names( obj: CriticalFormula ): Set[VarOrConst] =
      containedNames( obj.skTerm ) ++ containedNames( obj.term )
  }

  implicit object checkable extends Checkable[CriticalFormula] {
    override def check( cf: CriticalFormula )( implicit ctx: Context ): Unit = {
      ctx.check( cf.term )
      ctx.check( cf.skTerm )
      require(
        ctx.skolemDef( cf.skSym ).isDefined,
        s"${cf.skSym} is not a Skolem symbol" )
    }
  }
}

case class EpsilonProof( criticalFormulas: Vector[CriticalFormula], shallow: HOLSequent, epsilonized: HOLSequent ) {
  require( shallow.sizes == epsilonized.sizes )

  def toSigRelativeString( implicit sig: BabelSignature ): String = {
    val exporter = new BabelExporter( unicode = true, sig = sig )
    import exporter._
    Doc.stack(
      criticalFormulas.
        groupBy( _.skTerm ).values.toVector.
        sortBy( _.head.skSym.name ).
        map( cfs => nest( show( cfs.head.skTerm ) <+> "→" </>
          Doc.wordwrap( cfs.map( cf => show( cf.term ) ), " |" ) ) )
        :+ show( epsilonized )
        :+ show( shallow ) ).render( lineWidth )
  }
  override def toString: String = toSigRelativeString

  def deep( implicit ctx: Context ): HOLSequent =
    criticalFormulas.map( _.deep ) ++: epsilonized
}

object EpsilonProof {
  implicit object closedUnderSubstitution extends ClosedUnderSub[EpsilonProof] {
    override def applySubstitution( sub: Substitution, arg: EpsilonProof ): EpsilonProof =
      EpsilonProof( sub( arg.criticalFormulas ), shallow = sub( arg.shallow ), epsilonized = sub( arg.epsilonized ) )
  }
  implicit object closedUnderReplacement extends ClosedUnderReplacement[EpsilonProof] {
    override def replace( obj: EpsilonProof, p: PartialFunction[Expr, Expr] ): EpsilonProof =
      EpsilonProof(
        TermReplacement( obj.criticalFormulas, p ),
        TermReplacement( obj.shallow, p ), TermReplacement( obj.epsilonized, p ) )

    override def names( obj: EpsilonProof ): Set[VarOrConst] =
      containedNames( obj.criticalFormulas ) ++ containedNames( obj.shallow ) ++ containedNames( obj.epsilonized )
  }
  implicit object checkable extends Checkable[EpsilonProof] {
    override def check( p: EpsilonProof )( implicit ctx: Context ): Unit = {
      for ( cf <- p.criticalFormulas ) ctx.check( cf )

      val ctxWithEpsilonDefs = ctx.newMutable
      val epsilonized2 = epsilonize( p.shallow )( ctxWithEpsilonDefs )
      ctxWithEpsilonDefs += EpsilonC( TVar( "a" ) )
      ctxWithEpsilonDefs += ( ctx => ctx.state.update[Context.Reductions]( _ ++
        ctx.get[SkolemFunctions].epsilonDefinitions.map( ReductionRule( _ ) ) ) )
      for ( ( eps, sh ) <- p.epsilonized zip epsilonized2 )
        Checkable.requireDefEq( eps, sh )( ctxWithEpsilonDefs )
    }
  }
}

object epsilonize {

  def getSkTerm( quantified: Formula )( implicit ctx: MutableContext ): Expr = {
    val fvs = freeVariables( quantified ).toSeq.sortBy( _.name )
    val skD = Abs.Block( fvs, quantified )
    ctx.addSkolemSym( skD )( fvs )
  }

  def apply1( quantified: Formula )( implicit ctx: MutableContext ): Formula =
    instantiate( quantified, getSkTerm( quantified ) )

  def apply( f: Formula )( implicit ctx: MutableContext ): Formula =
    f match {
      case Bottom() | Top() | Atom( _, _ ) => f
      case Neg( a )                        => -apply( a )
      case And( a, b )                     => apply( a ) & apply( b )
      case Or( a, b )                      => apply( a ) | apply( b )
      case Imp( a, b )                     => apply( a ) --> apply( b )

      case Quant( x, sub, isAll ) =>
        apply1( Quant( x, apply( sub ), isAll ) )
    }

  def apply( s: HOLSequent )( implicit ctx: MutableContext ): HOLSequent =
    s.map( epsilonize( _ ) )

}

object ExpansionProofToEpsilon {

  /**
   * Compute a replacement for sk1 using only sk2.
   * Typical result is something like `λx λy sk2(y, x)`.
   */
  private def matchSkDefs( sk1: Const, def1: Expr, sk2: Const, def2: Expr )( implicit ctx0: Context ): Expr = {
    implicit val ctx: MutableContext = ctx0.newMutable
    val def1_ = def1 match {
      case Abs.Block( xs, Quant( x, sub, isAll ) ) =>
        Abs.Block( xs, Quant( x, epsilonize( sub ), isAll ) )
    }
    val ( Abs.Block( vs1, q1 ), Abs.Block( vs2, q2 ) ) =
      TermReplacement( ( def1_, def2 ), ctx.get[SkolemFunctions].epsilonDefinitions.toMap )
    val Some( subst ) = syntacticMatching( normalize( q2 ), normalize( q1 ) )
    Abs.Block( vs1, subst( sk2( vs2 ) ) )
  }

  def apply( e: ExpansionProof )( implicit ctx: MutableContext ): EpsilonProof = {
    val shallow = e.nonCutPart.shallow
    val epsilonized = epsilonize( shallow )

    val critFormulas = mutable.Buffer[CriticalFormula]()
    val repl = mutable.Map[Expr, Expr]()
    val evSubstMap = mutable.Map[Var, Expr]()
    def gather( e: ExpansionTree, f: Formula ): Unit =
      ( e, f ) match {
        case ( ETAtom( _, _ ) | ETWeakening( _, _ ) | ETTop( _ ) | ETBottom( _ ), g ) =>
        case ( ETMerge( a, b ), g ) =>
          gather( a, f ); gather( b, g )
        case ( ETNeg( a ), Neg( ga ) ) => gather( a, ga )
        case ( ETAnd( a, b ), And( ga, gb ) ) =>
          gather( a, ga ); gather( b, gb )
        case ( ETOr( a, b ), Or( ga, gb ) ) =>
          gather( a, ga ); gather( b, gb )
        case ( ETImp( a, b ), Imp( ga, gb ) ) =>
          gather( a, ga ); gather( b, gb )
        case ( ETWeakQuantifier( sh, insts ), Quant( x, sub, isAll ) ) =>
          val Some( subst ) = syntacticMatching( f, sh )
          for ( ( inst, ch ) <- insts ) {
            gather( ch, sub )
            val skT = epsilonize.getSkTerm( Quant( x, epsilonize( sub ), isAll ) )
            critFormulas += CriticalFormula( subst( skT ), inst )
          }
        case ( e @ ETSkolemQuantifier( _, _, skD, ch ), Quant( x, sub, isAll ) ) =>
          val Apps( newSkC: Const, _ ) = epsilonize.getSkTerm( Quant( x, epsilonize( sub ), isAll ) )
          repl( e.skolemConst ) = matchSkDefs( e.skolemConst, skD, newSkC, ctx.skolemDef( newSkC ).get )
          gather( ch, sub )
        case ( ETStrongQuantifier( sh, v, ch ), Quant( x, sub, isAll ) ) =>
          val Some( subst ) = syntacticMatching( f, sh )
          evSubstMap( v ) = subst( epsilonize.getSkTerm( Quant( x, epsilonize( sub ), isAll ) ) )
          gather( ch, sub )
      }

    for ( et <- e.nonCutPart ) gather( et, et.shallow )
    for ( cut <- e.cuts ) gather( cut, cut.shallow )

    val p0 = EpsilonProof( critFormulas.toVector, shallow = shallow, epsilonized = epsilonized )

    val evSubst = e.linearizedDependencyRelation.foldRight( Substitution() )( ( ev, evSubst0 ) =>
      Substitution( ev -> evSubstMap( ev ) ) compose evSubst0 )
    val p1 = evSubst( p0 )

    if ( repl.isEmpty ) p1 else
      TermReplacement( p1, { case t => BetaReduction.betaNormalize( TermReplacement( t, repl ) ) } )
  }

}

object LKProofToEpsilon {
  def apply( p: LKProof )( implicit ctx: MutableContext ): EpsilonProof =
    ExpansionProofToEpsilon( LKToExpansionProof( p ) )
}
