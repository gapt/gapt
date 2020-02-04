package gapt.logic.hol

import gapt.expr.{ BetaReduction, Var, VarOrConst }
import gapt.expr.formula.{ All, And, Atom, Bottom, Eq, Ex, Formula, Imp, MonoidalBinaryPropConnectiveHelper, Neg, Or, Quant, Top }
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.hol.containsStrongQuantifier
import gapt.expr.subst.Substitution
import gapt.logic.Polarity
import gapt.proofs.FOLClause
import gapt.proofs.HOLClause
import gapt.proofs.Sequent
import gapt.proofs.resolution.Input
import gapt.proofs.resolution.structuralCNF

/**
 * Transforms a formula to negation normal form (transforming also
 * implications into disjunctions)
 */
object toNNF {
  def apply( f: Formula ): Formula = f match {
    case Top() | Bottom() => f
    case Atom( _, _ )     => f
    case Imp( f1, f2 )    => Or( toNNF( Neg( f1 ) ), toNNF( f2 ) )
    case And( f1, f2 )    => And( toNNF( f1 ), toNNF( f2 ) )
    case Or( f1, f2 )     => Or( toNNF( f1 ), toNNF( f2 ) )
    case Ex( x, f )       => Ex( x, toNNF( f ) )
    case All( x, f )      => All( x, toNNF( f ) )
    case Neg( f ) => f match {
      case Top()         => Bottom()
      case Bottom()      => Top()
      case Atom( _, _ )  => Neg( f )
      case Neg( f1 )     => toNNF( f1 )
      case Imp( f1, f2 ) => And( toNNF( f1 ), toNNF( Neg( f2 ) ) )
      case And( f1, f2 ) => Or( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Or( f1, f2 )  => And( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Ex( x, f )    => All( x, toNNF( Neg( f ) ) )
      case All( x, f )   => Ex( x, toNNF( Neg( f ) ) )
      case _             => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
    }
    case _ => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

/**
 * Simplify a Formula using the equations for bottom and top as
 * well as idempotence of conjunction and disjunction.
 */
object simplify {
  def apply( f: Formula ): Formula = toNNF( f ) match {
    case And.nAry( conjuncts ) if conjuncts.length >= 2 => simplifyMonoidalBinaryPropConnective( conjuncts, And, Or )
    case Or.nAry( disjuncts ) if disjuncts.length >= 2  => simplifyMonoidalBinaryPropConnective( disjuncts, Or, And )

    case Quant( x, innerFormula, isAll )                => simplifyQuantifier( x, innerFormula, isAll )

    case n @ Neg( s ) => simplify( s ) match {
      case Top()    => Bottom()
      case Bottom() => Top()
      case _        => n
    }
    case Eq( l, r ) if l == r               => Top()
    case Eq( l: VarOrConst, r: VarOrConst ) => Eq( List( l, r ).minBy( _.name ), List( l, r ).maxBy( _.name ) )
    case p                                  => p
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]

  private def simplifyMonoidalBinaryPropConnective(
    arguments:      List[Formula],
    connective:     MonoidalBinaryPropConnectiveHelper,
    dualConnective: MonoidalBinaryPropConnectiveHelper ): Formula = {
    val simplifiedArguments = arguments.map( simplify( _ ) )
    val dualNeutral = dualConnective.neutral().asInstanceOf[Formula]
    if ( simplifiedArguments.contains( dualNeutral ) || containsPropAndItsNegation( simplifiedArguments ) )
      dualNeutral
    else {
      val neutralRemoved = simplifiedArguments.toSet.filterNot( _ == connective.neutral() )
      val absorbedRemoved = neutralRemoved.filterNot {
        case dualConnective.nAry( dualArguments ) if dualArguments.length >= 2 => dualArguments.exists( neutralRemoved.contains )
        case _ => false
      }
      connective( absorbedRemoved )
    }
  }

  private def simplifyQuantifier( variable: Var, innerFormula: Formula, isAll: Boolean ): Formula = {
    val simplificationConnective = if ( isAll ) Or else And
    val formula @ simplificationConnective.nAry( arguments ) = simplify( innerFormula )
    object UnaryPolarityConnective {
      def unapply( formula: Formula ): Option[Formula] = if ( isAll ) Neg.unapply( formula ) else Some( formula )
    }
    arguments.collectFirst {
      case UnaryPolarityConnective( Eq( lhs, rhs ) ) if lhs == variable || rhs == variable =>
        val substitute = if ( lhs == variable ) rhs else lhs
        val substitution = Substitution( variable -> substitute )
        simplify( BetaReduction.betaNormalize( substitution( simplificationConnective( arguments ) ) ) )
    }.getOrElse( formula match {
      case _ if !formula.contains( variable ) => formula
      case _                                  => Quant( variable, formula, isAll )
    } )
  }

  private def containsPropAndItsNegation( formulas: Seq[Formula] ): Boolean =
    formulas.exists( p => formulas.contains( simplify( Neg( p ) ) ) )
}

/**
 * Computes a positive CNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = {
    require( !containsStrongQuantifier( f, Polarity.Negative ), s"Formula contains strong quantifiers: $f" )
    structuralCNF.onProofs( Seq( Input( Sequent() :+ f ) ), propositional = false, structural = false ).
      map( _.conclusion.map( _.asInstanceOf[Atom] ) )
  }
}

/**
 * Computes a negative CNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFp( -f )
}

/**
 * Computes a positive DNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFn( f ).map( _.swapped )
}

/**
 * Computes a negative DNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFp( f ).map( _.swapped )
}

