package gapt.proofs.expansion
import gapt.expr.VarOrConst
import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.formats.babel.BabelSignature
import gapt.logic.Polarity
import gapt.utils.Doc

import scala.runtime.ScalaRunTime

/**
 * Expansion tree term.
 *
 * This is a compressed representation of expansion trees that does not
 * store formulas or polarity information.
 *
 * In contrast to expansion trees, expansion tree terms do not have shallow
 * and deep formulas.  Rather, there is a (partial) function from term and shallow
 * formula (and polarity) to deep formula.
 *
 * For example, instead of `ETAtom(hof"P(a)", Polarity.Positive)`,
 * we just store `ETtAtom`.
 *
 * As a side effect, the [[deep]] methods checks whether an expansion tree
 * term is correct for a given shallow formula (it throws an exception if
 * the term is not correct).
 */
sealed abstract class ETt { self: Product =>
  override val hashCode: Int = ScalaRunTime._hashCode( self )

  def foreach( f: ETt => Unit ): Unit = {
    f( this )
    this match {
      case ETtAtom | ETtWeakening | ETtNullary =>
      case ETtMerge( a, b ) =>
        a.foreach( f ); b.foreach( f )
      case ETtUnary( a ) => a.foreach( f )
      case ETtBinary( a, b ) =>
        a.foreach( f ); b.foreach( f )
      case ETtWeak( insts )   => insts.values.foreach( _.foreach( f ) )
      case ETtStrong( _, ch ) => ch.foreach( f )
      case ETtSkolem( _, ch ) => ch.foreach( f )
      case ETtDef( _, ch )    => ch.foreach( f )
    }
  }

  def eigenVariables: Set[Var] = {
    val result = Set.newBuilder[Var]
    foreach {
      case ETtStrong( eigenVar, _ ) => result += eigenVar
      case _                        =>
    }
    result.result()
  }

  def deep( shallow: Formula, polarity: Polarity ): Formula =
    ( ( this, shallow ): @unchecked ) match {
      case ( ETtAtom, _ )      => shallow

      case ( ETtWeakening, _ ) => if ( polarity.positive ) Bottom() else Top()
      case ( ETtMerge( a, b ), _ ) =>
        val d1 = a.deep( shallow, polarity )
        val d2 = b.deep( shallow, polarity )
        if ( polarity.positive ) d1 | d2 else d1 & d2

      case ( ETtNullary, Top() | Bottom() ) => shallow
      case ( ETtUnary( ch1 ), Neg( sh1 ) )  => -ch1.deep( sh1, !polarity )
      case ( ETtBinary( ch1, ch2 ), And( sh1, sh2 ) ) =>
        ch1.deep( sh1, polarity ) & ch2.deep( sh2, polarity )
      case ( ETtBinary( ch1, ch2 ), Or( sh1, sh2 ) ) =>
        ch1.deep( sh1, polarity ) | ch2.deep( sh2, polarity )
      case ( ETtBinary( ch1, ch2 ), Imp( sh1, sh2 ) ) =>
        ch1.deep( sh1, !polarity ) --> ch2.deep( sh2, polarity )

      case ( ETtWeak( insts ), Quant( bv, sh, isAll ) ) if isAll == polarity.negative =>
        import gapt.expr.subst.ExprSubstWithβ._
        val ds = for ( ( inst, ch ) <- insts )
          yield ch.deep( Substitution( bv -> inst )( sh ), polarity )
        if ( polarity.positive ) Or( ds ) else And( ds )
      case ( ETtStrong( ev, ch ), Quant( bv, sh, isAll ) ) if isAll == polarity.positive =>
        ch.deep( Substitution( bv -> ev )( sh ), polarity )
      case ( ETtSkolem( skT, ch ), Quant( bv, sh, isAll ) ) if isAll == polarity.positive =>
        ch.deep( Substitution( bv -> skT )( sh ), polarity )

      case ( ETtDef( sh, ch ), _ ) => ch.deep( sh, polarity )
    }

  def toDoc( implicit sig: BabelSignature ): Doc = new ETtPrettyPrinter( sig ).export( this )
  def toSigRelativeString( implicit sig: BabelSignature ): String = toDoc.render( 80 )
  override def toString: String = toSigRelativeString
}

object ETt {
  implicit object closedUnderSubst extends ClosedUnderSub[ETt] {
    def applySubstitution( sub: Substitution, et: ETt ): ETt = et match {
      case ETtAtom | ETtNullary | ETtWeakening => et
      case ETtMerge( child1, child2 ) =>
        ETtMerge( applySubstitution( sub, child1 ), applySubstitution( sub, child2 ) )
      case ETtUnary( child ) =>
        ETtUnary( applySubstitution( sub, child ) )
      case ETtBinary( child1, child2 ) =>
        ETtBinary( applySubstitution( sub, child1 ), applySubstitution( sub, child2 ) )
      case ETtWeak( instances ) =>
        ETtWeak.withMerge( for ( ( inst, ch ) <- instances.view )
          yield sub( inst ) -> applySubstitution( sub, ch ) )
      case ETtStrong( eigenVar, child ) =>
        sub( eigenVar ) match {
          case eigenVar2: Var =>
            ETtStrong( eigenVar2, applySubstitution( sub, child ) )
          case skTerm =>
            ETtSkolem( skTerm, applySubstitution( sub, child ) )
        }
      case ETtSkolem( skTerm, child ) =>
        ETtSkolem( sub( skTerm ), applySubstitution( sub, child ) )
      case ETtDef( sh, ch ) =>
        ETtDef( sub( sh ), applySubstitution( sub, ch ) )
    }
  }

  implicit object closedUnderRepl extends ClosedUnderReplacement[ETt] {
    def replace( tree: ETt, p: PartialFunction[Expr, Expr] ): ETt = tree match {
      case ETtAtom | ETtNullary | ETtWeakening => tree
      case ETtMerge( a, b )                    => ETtMerge( replace( a, p ), replace( b, p ) )
      case ETtUnary( a )                       => ETtUnary( replace( a, p ) )
      case ETtBinary( a, b )                   => ETtBinary( replace( a, p ), replace( b, p ) )
      case ETtWeak( insts ) => ETtWeak.withMerge( for ( ( inst, child ) <- insts.view )
        yield TermReplacement( inst, p ) -> replace( child, p ) )
      case ETtStrong( eigenVar, child ) =>
        ETtStrong( TermReplacement( eigenVar, p ).asInstanceOf[Var], replace( child, p ) )
      case ETtSkolem( skTerm, child ) =>
        ETtSkolem( TermReplacement( skTerm, p ), replace( child, p ) )
      case ETtDef( shallow, child ) => ETtDef( TermReplacement( shallow, p ), replace( child, p ) )
    }

    def names( tree: ETt ): Set[VarOrConst] = tree match {
      case ETtAtom | ETtNullary | ETtWeakening => Set.empty
      case ETtMerge( a, b )                    => names( a ) union names( b )
      case ETtUnary( a )                       => names( a )
      case ETtBinary( a, b )                   => names( a ) union names( b )
      case ETtWeak( insts ) =>
        ( insts.keys.flatMap( containedNames( _ ) ) ++ insts.values.flatMap( names ) ).toSet
      case ETtStrong( eigenVar, child ) => names( child ) + eigenVar
      case ETtSkolem( skTerm, child )   => names( child ) union containedNames( skTerm )
      case ETtDef( shallow, child )     => names( child ) union containedNames( shallow )
    }
  }
}

/** Expansion tree term for an atom. */
case object ETtAtom extends ETt

/** Expansion tree term for a weakening. */
case object ETtWeakening extends ETt
/** Expansion tree term for a merge. */
case class ETtMerge( child1: ETt, child2: ETt ) extends ETt

/** Expansion tree term for nullary connectives, i.e., ⊤ and ⊥. */
case object ETtNullary extends ETt
/** Expansion tree term for unary connectives, i.e., ¬. */
case class ETtUnary( child: ETt ) extends ETt
/** Expansion tree term for binary connectives, i.e., ∧, ∨, and →. */
case class ETtBinary( child1: ETt, child2: ETt ) extends ETt

/** Expansion tree term for weak quantifiers instances. */
case class ETtWeak( instances: Map[Expr, ETt] ) extends ETt
/** Expansion tree term for strong quantifiers with eigenvariables. */
case class ETtStrong( eigenVar: Var, child: ETt ) extends ETt
/** Expansion tree term for strong quantifiers with Skolem terms. */
case class ETtSkolem( skTerm: Expr, child: ETt ) extends ETt

/**
 * Expansion tree term for definitions.
 *
 * @param shallow The shallow formula for `child`
 */
case class ETtDef( shallow: Formula, child: ETt ) extends ETt

object ETtMerge {
  def apply( children: ETt* ): ETt = apply( children )
  def apply( children: Iterable[ETt] ): ETt =
    children.reduceLeftOption( ETtMerge( _, _ ) ).getOrElse( ETtWeakening )
}

object ETtWeak {
  def apply( instances: ( Expr, ETt )* ): ETtWeak = ETtWeak( instances.toMap )
  def withMerge( instances: Iterable[( Expr, ETt )] ): ETt =
    ETtWeak( Map() ++ instances.groupBy( _._1 ).view.mapValues( chs => ETtMerge( chs.map( _._2 ) ) ).toMap )
}

