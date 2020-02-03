package gapt.logic.hol

import gapt.expr.BetaReduction
import gapt.expr.formula.{ All, And, Atom, Bottom, Eq, Ex, Formula, Imp, Neg, Or, Quant, Top }
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
  def apply( f: Formula ): Formula = toNNF(f) match {
    case And(a, Or(b, c)) if a isSimplifiedEqualToOneOf(b, c) => simplify(a)
    case And(Or(b, c), a) if a isSimplifiedEqualToOneOf(b, c) => simplify(a)
    case Or(a, And(b, c)) if a isSimplifiedEqualToOneOf(b, c) => simplify(a)
    case Or(And(b, c), a) if a isSimplifiedEqualToOneOf(b, c) => simplify(a)

    case All(x, Or(Neg(Eq(l, r)), p)) if x == l => simplify(BetaReduction.betaNormalize(Substitution(x -> r)(p)))
    case All(x, Or(Neg(Eq(l, r)), p)) if x == r => simplify(BetaReduction.betaNormalize(Substitution(x -> l)(p)))
    case All(x, Or(Neg(p), Neg(Eq(l, r)))) if x == l => simplify(BetaReduction.betaNormalize(Substitution(x -> r)(Neg(p))))
    case All(x, Or(Neg(p), Neg(Eq(l, r)))) if x == r => simplify(BetaReduction.betaNormalize(Substitution(x -> l)(Neg(p))))

    case Ex(x, Eq(l, r)) if x == l || x == r => Top()

    case And( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), r )       => r
      case ( r, Top() )       => r
      case ( Bottom(), _ )    => Bottom()
      case ( _, Bottom() )    => Bottom()
      case ( l, r ) if l == r => l
      case ( l, r )           => And( l, r )
    }
    case Or( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), _ )       => Top()
      case ( _, Top() )       => Top()
      case ( Bottom(), r )    => r
      case ( r, Bottom() )    => r
      case ( l, r ) if l == r => l
      case ( l, r )           => Or( l, r )
    }
    case n @ Neg( s ) => simplify( s ) match {
      case Top()    => Bottom()
      case Bottom() => Top()
      case _ => n
    }
    case Quant( x, g, isAll ) =>
      simplify( g ) match {
        case Top()    => Top()
        case Bottom() => Bottom()
        case g_       => Quant( x, g_, isAll )
      }
    case Eq(l, r) if l == r => Top()
    case p => p
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]

  private implicit class FormulaHelper(formula: Formula)
  {
    def isSimplifiedEqualToOneOf(formulas: Formula*): Boolean = {
      val simplified = simplify( formula )
      formulas.map( simplify( _ ) ).contains( simplified )
    }
  }
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

