package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature }
import at.logic.gapt.utils.Doc

case class Hyp( idx: Int ) extends AnyVal {
  def inAnt = idx < 0
  def inSuc = !inAnt
  def polarity = if ( inAnt ) Polarity.InAntecedent else Polarity.InSuccedent
  def replace( a: Hyp, b: Hyp ): Hyp = if ( this == a ) b else this
  def toDoc: Doc = toString
  override def toString = if ( idx < 0 ) idx.toString else "+" + idx.toString
}
object Hyp {
  def mk( idx: Int, polarity: Polarity ): Hyp = mk( idx, polarity.inSuc )
  def mk( idx: Int, inSuc: Boolean ): Hyp = if ( inSuc ) Hyp( idx ) else Hyp( -idx )
}

trait Bound {
  def freeHyps: Set[Hyp]
  def toDoc( implicit sig: BabelSignature ): Doc
}
final case class Bound1( aux: Hyp, p: LKt ) extends Bound {
  def freeHyps: Set[Hyp] = p.freeHyps - aux
  def rename( awayFrom: Iterable[Hyp] ): Bound1 = {
    val aux_ = ( p.freeHyps ++ awayFrom ).freshSameSide( aux )
    Bound1( aux_, p.replace( aux, aux_ ) )
  }
  def replace( a: Hyp, b: Hyp ): Bound1 =
    if ( a == aux ) this
    else if ( b == aux ) rename( List( b ) ).replace( a, b )
    else Bound1( aux, p.replace( a, b ) )

  def inst( b: Hyp ): LKt = p.replace( aux, b )
  def isConst: Boolean = !p.freeHyps( aux )

  def toDoc( implicit sig: BabelSignature ): Doc =
    aux.toDoc <> ":" <+> p.toDoc
}
final case class Bound2( aux1: Hyp, aux2: Hyp, p: LKt ) extends Bound {
  require( aux1 != aux2 )
  def freeHyps: Set[Hyp] = p.freeHyps - aux1 - aux2
  def rename( awayFrom: Iterable[Hyp] ): Bound2 = {
    val free = p.freeHyps ++ awayFrom + aux1 + aux2
    val aux1_ = free.freshSameSide( aux1 )
    val aux2_ = ( free + aux1_ ).freshSameSide( aux2 )
    Bound2( aux1_, aux2_, p.replace( aux1, aux1_ ).replace( aux2, aux2_ ) )
  }
  def replace( a: Hyp, b: Hyp ): Bound2 =
    if ( a == aux1 || a == aux2 ) this
    else if ( b == aux1 || b == aux2 ) rename( Set( b ) ).replace( a, b )
    else Bound2( aux1, aux2, p.replace( a, b ) )

  def toDoc( implicit sig: BabelSignature ): Doc =
    aux1.toDoc <> ":" <+> aux2.toDoc <> ":" <+> p.toDoc
}
final case class BoundN( auxs: List[Hyp], p: LKt ) extends Bound {
  def freeHyps: Set[Hyp] = p.freeHyps -- auxs
  def rename( awayFrom: Iterable[Hyp] ): BoundN = {
    val free = p.freeHyps ++ awayFrom ++ auxs
    val auxs_ = free.freshSameSide( auxs )
    BoundN( auxs_, auxs.view.zip( auxs_ ).foldLeft( p )( ( p_, a ) => p_.replace( a._1, a._2 ) ) )
  }
  def replace( a: Hyp, b: Hyp ): BoundN =
    if ( auxs.contains( a ) ) this
    else if ( auxs.contains( b ) ) rename( Set( b ) ).replace( a, b )
    else BoundN( auxs, p.replace( a, b ) )

  def toDoc( implicit sig: BabelSignature ): Doc =
    Doc.spread( auxs.map( aux => aux.toDoc <> ":" ) :+ p.toDoc )
}

sealed trait LKt {
  def replace( a: Hyp, b: Hyp ): LKt =
    this match {
      case _ if !freeHyps( a )            => this
      case Cut( f, q1, q2 )               => Cut( f, q1.replace( a, b ), q2.replace( a, b ) )
      case Ax( main1, main2 )             => Ax( main1.replace( a, b ), main2.replace( a, b ) )
      case Rfl( main )                    => Rfl( main.replace( a, b ) )
      case TopR( main )                   => TopR( main.replace( a, b ) )
      case NegR( main, q )                => NegR( main.replace( a, b ), q.replace( a, b ) )
      case NegL( main, q )                => NegL( main.replace( a, b ), q.replace( a, b ) )
      case AndR( main, q1, q2 )           => AndR( main.replace( a, b ), q1.replace( a, b ), q2.replace( a, b ) )
      case AndL( main, q )                => AndL( main.replace( a, b ), q.replace( a, b ) )
      case AllL( main, term, q )          => AllL( main.replace( a, b ), term, q.replace( a, b ) )
      case AllR( main, ev, q )            => AllR( main.replace( a, b ), ev, q.replace( a, b ) )
      case Eql( main, eq, ltr, rwCtx, q ) => Eql( main.replace( a, b ), eq.replace( a, b ), ltr, rwCtx, q.replace( a, b ) )
      case AllSk( main, term, skDef, q )  => AllSk( main.replace( a, b ), term, skDef, q.replace( a, b ) )
      case Def( main, f, q )              => Def( main.replace( a, b ), f, q.replace( a, b ) )
      case Ind( main, f, t, cs )          => Ind( main.replace( a, b ), f, t, cs.map( c => c.copy( q = c.q.replace( a, b ) ) ) )
      case Link( mains, name )            => Link( mains.map( _.replace( a, b ) ), name )
    }

  def mainHyps: Seq[Hyp] = this match {
    case Cut( _, _, _ )           => Seq()
    case Ax( main1, main2 )       => Seq( main1, main2 )
    case Rfl( main )              => Seq( main )
    case TopR( main )             => Seq( main )
    case NegL( main, _ )          => Seq( main )
    case NegR( main, _ )          => Seq( main )
    case AndL( main, _ )          => Seq( main )
    case AndR( main, _, _ )       => Seq( main )
    case AllL( main, _, _ )       => Seq( main )
    case AllR( main, _, _ )       => Seq( main )
    case Eql( main, eq, _, _, _ ) => Seq( main, eq )
    case AllSk( main, _, _, _ )   => Seq( main )
    case Def( main, _, _ )        => Seq( main )
    case Ind( main, _, _, _ )     => Seq( main )
    case Link( mains, _ )         => mains
  }

  val freeHyps: Set[Hyp] = this match {
    case Cut( _, q1, q2 )         => q1.freeHyps union q2.freeHyps
    case Ax( main1, main2 )       => Set( main1, main2 )
    case Rfl( main )              => Set( main )
    case TopR( main )             => Set( main )
    case NegL( main, q )          => q.freeHyps + main
    case NegR( main, q )          => q.freeHyps + main
    case AndL( main, q )          => q.freeHyps + main
    case AndR( main, q1, q2 )     => q1.freeHyps union q2.freeHyps + main
    case AllL( main, _, q )       => q.freeHyps + main
    case AllR( main, _, q )       => q.freeHyps + main
    case Eql( main, eq, _, _, q ) => q.freeHyps + main + eq
    case AllSk( main, _, _, q )   => q.freeHyps + main
    case Def( main, _, q )        => q.freeHyps + main
    case Ind( main, _, _, cs )    => cs.view.flatMap( _.q.freeHyps ).toSet + main
    case Link( mains, _ )         => mains.toSet
  }

  val hasCuts: Boolean = this match {
    case Cut( _, _, _ )                    => true
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => false
    case NegL( _, q )                      => q.p.hasCuts
    case NegR( _, q )                      => q.p.hasCuts
    case AndL( _, q )                      => q.p.hasCuts
    case AndR( _, q1, q2 )                 => q1.p.hasCuts || q2.p.hasCuts
    case AllL( _, _, q )                   => q.p.hasCuts
    case AllR( _, _, q )                   => q.p.hasCuts
    case Eql( _, _, _, _, q )              => q.p.hasCuts
    case AllSk( _, _, _, q )               => q.p.hasCuts
    case Def( _, _, q )                    => q.p.hasCuts
    case Ind( _, _, _, cs )                => cs.exists( _.q.p.hasCuts )
    case Link( _, _ )                      => false
  }

  val freeVars: Set[Var] = this match {
    case Cut( f, q1, q2 )                  => freeVariables( f ) union q1.p.freeVars union q2.p.freeVars
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => Set()
    case NegR( _, q )                      => q.p.freeVars
    case NegL( _, q )                      => q.p.freeVars
    case AndR( _, q1, q2 )                 => q1.p.freeVars union q2.p.freeVars
    case AndL( _, q )                      => q.p.freeVars
    case AllL( _, term, q )                => q.p.freeVars union freeVariables( term )
    case AllR( _, ev, q )                  => q.p.freeVars - ev
    case Eql( _, _, _, rwCtx, q )          => q.p.freeVars union freeVariables( rwCtx )
    case AllSk( _, _, _, q )               => q.p.freeVars
    case Def( _, f, q )                    => q.p.freeVars union freeVariables( f )
    case Ind( _, _, _, cs )                => cs.view.flatMap( c => c.q.p.freeVars -- c.evs ).toSet
    case Link( _, name )                   => freeVariables( name )
  }

  def toDoc( implicit sig: BabelSignature ): Doc = {
    val prod = this.asInstanceOf[Product]
    ( Doc.text( prod.productPrefix ) <> "(" <> Doc.wordwrap2(
      prod.productIterator.toSeq.map {
        case expr: Expr =>
          new BabelExporter( unicode = true, sig = sig ).
            show( expr, knownType = false, Set(), Map() )._1.inPrec( 0 )
        case bnd: Bound => bnd.toDoc
        case hyp: Hyp   => hyp.toDoc
        case p: LKt     => p.toDoc
        case b: Boolean => b.toString: Doc
        case s: Seq[_] => Doc.wordwrap2( s.map {
          case h: Hyp => h.toDoc
          case IndCase( ctr, evs, q ) =>
            ( ( ctr +: evs ).map( _.name: Doc ) :+ q.toDoc ).reduce( _ <> ": " <> _ )
        }, "," )
      }, "," ) <> ")" ).nest( 1 )
  }

  def subProofs: Vector[LKt] = {
    val out = Vector.newBuilder[LKt]
    def gather( p: LKt ): Unit = {
      out += p
      p match {
        case Cut( _, q1, q2 ) =>
          gather( q1.p ); gather( q2.p )
        case Ax( _, _ )   =>
        case Rfl( _ )     =>
        case TopR( _ )    =>
        case NegR( _, q ) => gather( q.p )
        case NegL( _, q ) => gather( q.p )
        case AndR( _, q1, q2 ) =>
          gather( q1.p ); gather( q2.p )
        case AndL( _, q )         => gather( q.p )
        case AllL( _, _, q )      => gather( q.p )
        case AllR( _, _, q )      => gather( q.p )
        case Eql( _, _, _, _, q ) => gather( q.p )
        case AllSk( _, _, _, q )  => gather( q.p )
        case Def( _, _, q )       => gather( q.p )
        case Ind( _, _, _, cs )   => for ( c <- cs ) gather( c.q.p )
        case Link( _, _ )         =>
      }
    }
    gather( this )
    out.result()
  }

  override def toString = toDoc.render( 80 )
}
case class Cut( f: Formula, q1: Bound1, q2: Bound1 ) extends LKt
case class Ax( main1: Hyp, main2: Hyp ) extends LKt
case class Rfl( main: Hyp ) extends LKt
case class TopR( main: Hyp ) extends LKt
case class NegR( main: Hyp, q: Bound1 ) extends LKt
case class NegL( main: Hyp, q: Bound1 ) extends LKt
case class AndR( main: Hyp, q1: Bound1, q2: Bound1 ) extends LKt
case class AndL( main: Hyp, q: Bound2 ) extends LKt
case class AllL( main: Hyp, term: Expr, q: Bound1 ) extends LKt
case class AllR( main: Hyp, ev: Var, q: Bound1 ) extends LKt
case class Eql( main: Hyp, eq: Hyp, ltr: Boolean, rwCtx: Expr, q: Bound1 ) extends LKt
case class AllSk( main: Hyp, term: Expr, skDef: Expr, q: Bound1 ) extends LKt
case class Def( main: Hyp, f: Formula, q: Bound1 ) extends LKt
case class IndCase( ctr: Const, evs: List[Var], q: BoundN )
case class Ind( main: Hyp, f: Abs, term: Expr, cases: List[IndCase] ) extends LKt {
  def indTy = f.variable.ty
}
case class Link( mains: List[Hyp], name: Expr ) extends LKt

trait ImplicitInstances {
  implicit val closedUnderSubstitutionBound1: ClosedUnderSub[Bound1] =
    ( sub: Substitution, bnd: Bound1 ) => bnd.copy( p = sub( bnd.p ) )
  implicit val closedUnderSubstitutionBound2: ClosedUnderSub[Bound2] =
    ( sub: Substitution, bnd: Bound2 ) => bnd.copy( p = sub( bnd.p ) )
  implicit val closedUnderSubstitutionBoundN: ClosedUnderSub[BoundN] =
    ( sub, bnd ) => bnd.copy( p = sub( bnd.p ) )
  implicit val closedUnderSubstitutionIndCase: ClosedUnderSub[IndCase] =
    ( sub, indCase ) =>
      if ( sub.domain.intersect( indCase.evs.toSet ).nonEmpty )
        Substitution( sub.map -- indCase.evs, sub.typeMap )( indCase )
      else if ( sub.range.intersect( indCase.evs.toSet ).nonEmpty ) {
        val renaming = rename( indCase.evs, indCase.q.p.freeVars union sub.range union sub.domain )
        IndCase( indCase.ctr, indCase.evs.map( renaming ),
          Substitution( sub.map ++ renaming, sub.typeMap )( indCase.q ) )
      } else
        indCase.copy( q = sub( indCase.q ) )
  implicit val closedUnderSubstitution: ClosedUnderSub[LKt] =
    ( sub: Substitution, p: LKt ) => p match {
      case Cut( f, q1, q2 )                  => Cut( sub( f ), sub( q1 ), sub( q2 ) )
      case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => p
      case NegR( main, q )                   => NegR( main, sub( q ) )
      case NegL( main, q )                   => NegL( main, sub( q ) )
      case AndR( main, q1, q2 )              => AndR( main, sub( q1 ), sub( q2 ) )
      case AndL( main, q )                   => AndL( main, sub( q ) )
      case AllL( main, term, q )             => AllL( main, sub( term ), sub( q ) )
      case AllR( _, ev, _ ) if sub.domain.contains( ev ) =>
        Substitution( sub.map - ev, sub.typeMap )( p )
      case AllR( main, ev, q ) if sub.range.contains( ev ) =>
        val ev_ = rename( ev, q.p.freeVars union sub.range union sub.domain )
        AllR( main, ev_, Substitution( sub.map + ( ev -> ev_ ), sub.typeMap )( q ) )
      case AllR( main, ev, q )            => AllR( main, ev, sub( q ) )
      case Eql( main, eq, ltr, rwCtx, q ) => Eql( main, eq, ltr, sub( rwCtx ), sub( q ) )
      case AllSk( main, term, skDef, q )  => AllSk( main, sub( term ), skDef, sub( q ) )
      case Def( main, f, q )              => Def( main, sub( f ), sub( q ) )
      case Ind( main, f, term, cases )    => Ind( main, sub( f ).asInstanceOf[Abs], sub( term ), sub( cases ) )
      case Link( mains, name )            => Link( mains, sub( name ) )
    }

  implicit object replaceableBnd1 extends ClosedUnderReplacement[Bound1] {
    def replace( bnd: Bound1, repl: PartialFunction[Expr, Expr] ): Bound1 =
      bnd.copy( p = TermReplacement( bnd.p, repl )( replaceable ) )
    def names( bnd: Bound1 ): Set[VarOrConst] = containedNames( bnd.p )
  }
  implicit object replaceableBnd2 extends ClosedUnderReplacement[Bound2] {
    def replace( bnd: Bound2, repl: PartialFunction[Expr, Expr] ): Bound2 =
      bnd.copy( p = TermReplacement( bnd.p, repl )( replaceable ) )
    def names( bnd: Bound2 ): Set[VarOrConst] = containedNames( bnd.p )
  }
  implicit object replaceableBndN extends ClosedUnderReplacement[BoundN] {
    def replace( bnd: BoundN, repl: PartialFunction[Expr, Expr] ): BoundN =
      bnd.copy( p = TermReplacement( bnd.p, repl )( replaceable ) )
    def names( bnd: BoundN ): Set[VarOrConst] = containedNames( bnd.p )
  }
  implicit object replaceableIndCase extends ClosedUnderReplacement[IndCase] {
    def replace( indCase: IndCase, repl: PartialFunction[Expr, Expr] ): IndCase =
      IndCase(
        TermReplacement( indCase.ctr, repl ).asInstanceOf[Const],
        TermReplacement( indCase.evs, repl ).map( _.asInstanceOf[Var] ),
        TermReplacement( indCase.q, repl ) )
    def names( indCase: IndCase ): Set[VarOrConst] =
      containedNames( indCase.q ) ++ indCase.evs + indCase.ctr
  }
  implicit object replaceable extends ClosedUnderReplacement[LKt] {
    override def replace( p: LKt, repl: PartialFunction[Expr, Expr] ): LKt =
      p match {
        case Cut( f, q1, q2 )                  => Cut( TermReplacement( f, repl ), TermReplacement( q1, repl ), TermReplacement( q2, repl ) )
        case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => p
        case NegR( main, q )                   => NegR( main, TermReplacement( q, repl ) )
        case NegL( main, q )                   => NegL( main, TermReplacement( q, repl ) )
        case AndR( main, q1, q2 )              => AndR( main, TermReplacement( q1, repl ), TermReplacement( q2, repl ) )
        case AndL( main, q )                   => AndL( main, TermReplacement( q, repl ) )
        case AllL( main, term, q )             => AllL( main, TermReplacement( term, repl ), TermReplacement( q, repl ) )
        case AllR( main, ev, q )               => AllR( main, TermReplacement( ev, repl ).asInstanceOf[Var], TermReplacement( q, repl ) )
        case Eql( main, eq, ltr, rwCtx, q )    => Eql( main, eq, ltr, TermReplacement( rwCtx, repl ).asInstanceOf[Abs], TermReplacement( q, repl ) )
        case AllSk( main, term, skDef, q )     => AllSk( main, TermReplacement( term, repl ), TermReplacement( skDef, repl ), TermReplacement( q, repl ) )
        case Def( main, f, q )                 => Def( main, TermReplacement( f, repl ), TermReplacement( q, repl ) )
        case Ind( main, f, t, cases )          => Ind( main, TermReplacement( f, repl ).asInstanceOf[Abs], TermReplacement( t, repl ), TermReplacement( cases, repl ) )
        case Link( mains, name )               => Link( mains, TermReplacement( name, repl ) )
      }
    override def names( p: LKt ): Set[VarOrConst] =
      p match {
        case Cut( f, q1, q2 )                  => containedNames( f ) union containedNames( q1 ) union containedNames( q2 )
        case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => Set()
        case NegR( _, q )                      => containedNames( q )
        case NegL( _, q )                      => containedNames( q )
        case AndR( _, q1, q2 )                 => containedNames( q1 ) union containedNames( q2 )
        case AndL( _, q )                      => containedNames( q )
        case AllL( _, term, q )                => containedNames( q ) union containedNames( term )
        case AllR( _, ev, q )                  => containedNames( q ) + ev
        case Eql( _, _, _, rwCtx, q )          => containedNames( q ) union containedNames( rwCtx )
        case AllSk( _, term, skDef, q )        => containedNames( q ) union containedNames( term ) union containedNames( skDef )
        case Def( _, f, q )                    => containedNames( q ) union containedNames( f )
        case Ind( _, f, t, cases )             => containedNames( cases ) union containedNames( f ) union containedNames( t )
        case Link( _, name )                   => containedNames( name )
      }
  }
}
