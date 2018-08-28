package gapt.proofs.reduction

import gapt.expr._
import gapt.expr.hol._
import gapt.proofs._
import gapt.proofs.context.MutableContext
import gapt.proofs.expansion._
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution._
import gapt.utils.NameGenerator

import scala.collection.mutable

/**
 * Represents a reduction of a problem together with a back-translation of the solutions.
 *
 * A problem P1 is reduced to a problem P2, a solution S2 to the problem P2
 * can then be translated back to a solution S1 of the problem P1.
 */
trait Reduction[-P1, +P2, +S1, -S2] {
  def forward( problem: P1 ): ( P2, S2 => S1 )

  /** Sequentially composes reductions. */
  def |>[P2_ >: P2, P3, S2_ <: S2, S3]( other: Reduction[P2_, P3, S2_, S3] ): Reduction[P1, P3, S1, S3] =
    CombinedReduction( this, other )
}

/** A reduction that does not change the type of the problem. */
trait Reduction_[P, S] extends Reduction[P, P, S, S]
/** A reduction without back-translation. */
trait OneWayReduction_[P] extends Reduction[P, P, Nothing, Any]

/**
 * Sequential composition of reductions.
 *
 * This class is not intended to be used directly, but via the [[Reduction#|>]] operator.
 */
case class CombinedReduction[-P1, P2, +P3, +S1, S2, -S3](
    red1: Reduction[P1, P2, S1, S2],
    red2: Reduction[P2, P3, S2, S3] ) extends Reduction[P1, P3, S1, S3] {
  override def toString = s"$red1 |> $red2"

  override def forward( problem: P1 ): ( P3, S3 => S1 ) = {
    val ( prob2, back1 ) = red1.forward( problem )
    val ( prob3, back2 ) = red2.forward( prob2 )
    ( prob3, sol3 => back1( back2( sol3 ) ) )
  }
}

private class ErasureReductionHelper( constants: Set[Const] ) {
  val termErasure = constants map {
    case c @ Const( name, FunctionType( _, argTypes ), _ ) =>
      c -> FOLFunctionConst( s"f_$name", argTypes.size )
  } toMap
  val termReification = termErasure map { _.swap }

  val predicateErasure = constants collect {
    case c @ HOLAtomConst( name, argTypes ) =>
      c -> FOLAtomConst( s"P_$name", argTypes.size )
  } toMap
  val predicateReification = predicateErasure map { _.swap }

  private def renameFreeVars( vs: Set[Var] ) =
    vs.toSeq.zipWithIndex.map { case ( v, i ) => v -> FOLVar( s"${v.name}_$i" ) }.toMap

  def forward( sequent: HOLSequent ): FOLSequent = sequent map { f => forward( f, renameFreeVars( freeVariables( f ) ) ) }
  def forward( clause: HOLClause )( implicit dummyImplicit: DummyImplicit ): HOLClause = forward( clause, renameFreeVars( freeVariables( clause ) ) )
  def forward( clause: HOLClause, freeVars: Map[Var, FOLVar] ): FOLClause = clause map { forward( _, freeVars ).asInstanceOf[FOLAtom] }

  def forward( formula: Formula, freeVars: Map[Var, FOLVar] ): FOLFormula = formula match {
    case f @ Top()    => f
    case f @ Bottom() => f
    case Neg( f )     => Neg( forward( f, freeVars ) )
    case And( f, g )  => And( forward( f, freeVars ), forward( g, freeVars ) )
    case Or( f, g )   => Or( forward( f, freeVars ), forward( g, freeVars ) )
    case Imp( f, g )  => Imp( forward( f, freeVars ), forward( g, freeVars ) )
    case All( x, f ) =>
      val y = rename( FOLVar( x.name ), freeVars.values )
      All( y, forward( f, freeVars + ( x -> y ) ) )
    case Ex( x, f ) =>
      val y = rename( FOLVar( x.name ), freeVars.values )
      Ex( y, forward( f, freeVars + ( x -> y ) ) )
    case Eq( t, s ) => Eq( forward( t, freeVars ), forward( s, freeVars ) )
    case Apps( c: HOLAtomConst, args ) =>
      predicateErasure( c )( args map { forward( _, freeVars ) }: _* )
  }

  def forward( term: Expr, freeVars: Map[Var, FOLVar] ): FOLTerm = term match {
    case Apps( c: Const, args ) =>
      termErasure( c )( args map { forward( _, freeVars ) }: _* )
    case v: Var => freeVars( v )
  }

  def infer( formula: FOLFormula, known: Map[FOLVar, Var] ): Map[FOLVar, Var] =
    infer( formula, To, known )
  def infer( expr: FOLExpression, ty: Ty, known: Map[FOLVar, Var] ): Map[FOLVar, Var] = {
    val res = mutable.Map[FOLVar, Var]()
    res ++= known

    def i( f: FOLExpression, expected: Ty ): Ty = f match {
      case Eq( a @ FOLFunction( _, _ ), b ) =>
        i( b, i( a, null ) )
      case Eq( a, b @ FOLFunction( _, _ ) ) =>
        i( a, i( b, null ) )
      case Eq( a: FOLVar, b ) if known isDefinedAt a =>
        i( b, known( a ).ty )
      case Eq( a, b: FOLVar ) if known isDefinedAt b =>
        i( a, known( b ).ty )
      case Eq( a: FOLVar, b: FOLVar ) => i( b, i( a, Ti ) ) // hope for the best...
      case Apps( c: FOLAtomConst, args ) =>
        predicateReification( c ) match {
          case Const( _, FunctionType( _, argTypes ), _ ) =>
            for ( ( a: FOLTerm, t ) <- args zip argTypes )
              i( a, t )
        }
        expected
      case v @ FOLVar( name ) =>
        res.get( v ) match {
          case Some( Var( _, `expected` ) ) =>
          case Some( Var( _, other ) ) =>
            throw new Exception( s"Reification failure: $v should have type $expected but already has type $other instead" )
          case None => res( v ) = Var( name, expected )
        }
        expected
      case Apps( c: FOLFunctionConst, args ) =>
        termReification( c ) match {
          case Const( _, FunctionType( retType, argTypes ), _ ) =>
            for ( ( a: FOLTerm, t ) <- args zip argTypes )
              i( a, t )
            retType
        }
    }

    i( expr, ty )
    res.toMap
  }

  def infer( clause: FOLClause, known: Map[FOLVar, Var] ): Map[FOLVar, Var] =
    clause.elements.foldRight( known )( infer )

  def back( proof: ResolutionProof, originalInputs: Set[HOLClause] ): ResolutionProof = {
    import gapt.proofs.resolution._

    val memo = mutable.Map[( ResolutionProof, Map[FOLVar, Var] ), ResolutionProof]()

    def f( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = {
      g( p, freeVariables( p.conclusion ) map { case v: FOLVar => v -> vars( v ) } toMap )
    }

    def g( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = memo.getOrElseUpdate( ( p, vars ), p match {
      case Refl( term: FOLTerm ) => Refl( back( term, vars ) )
      case Taut( atom: FOLAtom ) => Taut( back( atom, vars ) )
      case Input( clause ) =>
        ( for (
          original <- originalInputs;
          subst <- syntacticMatching( original.toDisjunction, back( clause.toDisjunction.asInstanceOf[FOLFormula], vars ) )
        ) yield Subst.ifNecessary( Input( original ), subst ) ).head

      case Subst( subProof, subst ) =>
        val subProofVars = freeVariables( subProof.conclusion ).map {
          case v @ FOLVar( name ) =>
            v -> Var( name, subst( v ) match {
              case Apps( head: FOLFunctionConst, _ ) =>
                termReification( head ) match { case Const( _, FunctionType( retType, _ ), _ ) => retType }
              case u: FOLVar => vars( u ).ty
            } )
        }.toMap
        val subProof_ = f( subProof, subProofVars )
        val newSubst = Substitution( freeVariables( subProof.conclusion ) map {
          case v @ FOLVar( name ) =>
            subProofVars( v ) -> back( subst( v ).asInstanceOf[FOLTerm], vars )
        } )
        Subst( subProof_, newSubst )

      case Factor( subProof, idx1, idx2 ) =>
        Factor( f( subProof, vars ), idx1, idx2 )

      case Resolution( subProof1, idx1, subProof2, idx2 ) =>
        val subProofVars = infer( subProof1.conclusion( idx1 ).asInstanceOf[FOLAtom], vars )
        val q1 = f( subProof1, subProofVars )
        val q2 = f( subProof2, subProofVars )
        Resolution( q1, idx1, q2, idx2 )

      case Paramod( subProof1, eq, ltr, subProof2, lit, Abs( v: FOLVar, con: FOLAtom ) ) =>
        val subProofVars = infer( subProof1.conclusion( eq ).asInstanceOf[FOLAtom], vars )
        val q1 = f( subProof1, subProofVars )
        val q2 = f( subProof2, subProofVars )
        val conVars = infer( con, vars )
        val newCon = Abs( conVars( v ), back( con, conVars ) )
        Paramod( q1, eq, ltr, q2, lit, newCon )

      case Flip( subProof1, idx1 ) =>
        Flip( f( subProof1, vars ), idx1 )

      // FIXME: propositional
    } )

    f( proof, Map() )
  }

  def eigenVariables( et: ExpansionTree, shallow: Formula ): Map[FOLVar, Var] =
    ( et, shallow ) match {
      case ( ETAtom( _, _ ) | ETWeakening( _, _ ) | ETBottom( _ ) | ETTop( _ ), _ ) => Map()
      case ( ETMerge( a, b ), _ ) => eigenVariables( a, shallow ) ++ eigenVariables( b, shallow )
      case ( ETNeg( a ), Neg( sha ) ) => eigenVariables( a, sha )
      case ( ETAnd( a, b ), And( sha, shb ) ) => eigenVariables( a, sha ) ++ eigenVariables( b, shb )
      case ( ETOr( a, b ), Or( sha, shb ) ) => eigenVariables( a, sha ) ++ eigenVariables( b, shb )
      case ( ETImp( a, b ), Imp( sha, shb ) ) => eigenVariables( a, sha ) ++ eigenVariables( b, shb )
      case ( ETStrongQuantifier( _, ev: FOLVar, a ), All( shx, sha ) ) =>
        eigenVariables( a, sha ) + ( ev -> Var( ev.name, shx.ty ) )
      case ( ETWeakQuantifier( _, insts ), Quant( x, sh, isForall ) ) =>
        insts.flatMap { case ( _, a ) => eigenVariables( a, sh ) }
    }

  def back( et: ExpansionTree, shallow: Formula, freeVars: Map[FOLVar, Var] ): ExpansionTree = ( et, shallow ) match {
    case ( ETAtom( atom: FOLAtom, pol ), _ ) => ETAtom( back( atom, freeVars ), pol )
    case ( ETWeakening( _, pol ), _ )        => ETWeakening( shallow, pol )
    case ( ETMerge( a, b ), _ )              => ETMerge( back( a, shallow, freeVars ), back( b, shallow, freeVars ) )
    case ( _: ETBottom | _: ETTop, _ )       => et
    case ( ETNeg( a ), Neg( sha ) )          => ETNeg( back( a, sha, freeVars ) )
    case ( ETAnd( a, b ), And( sha, shb ) )  => ETAnd( back( a, sha, freeVars ), back( b, shb, freeVars ) )
    case ( ETOr( a, b ), Or( sha, shb ) )    => ETOr( back( a, sha, freeVars ), back( b, shb, freeVars ) )
    case ( ETImp( a, b ), Imp( sha, shb ) )  => ETImp( back( a, sha, freeVars ), back( b, shb, freeVars ) )
    case ( ETStrongQuantifier( _, ev: FOLVar, a ), All( shx, _ ) ) =>
      ETStrongQuantifier( shallow, freeVars( ev ), back( a, instantiate( shallow, freeVars( ev ) ), freeVars ) )
    case ( ETWeakQuantifier( _, insts ), Quant( x, sh, isForall ) ) =>
      ETWeakQuantifier(
        shallow,
        for ( ( t: FOLTerm, inst ) <- insts ) yield {
          val childFreeVars = infer( t, x.ty, freeVars )
          val t_ = back( t, childFreeVars )
          t_ -> back( inst, Substitution( x -> t_ )( sh ), childFreeVars )
        } )
  }

  def back( expansionProof: ExpansionProof, endSequent: HOLSequent ): ExpansionProof = {
    require( expansionProof.shallow isSubsetOf endSequent.map( forward( _, Map[Var, FOLVar]() ) ) )
    val evs = Map() ++ ( for {
      et <- expansionProof.expansionSequent.elements
      originalSh <- endSequent.elements
      if forward( originalSh, Map[Var, FOLVar]() ) == et.shallow
      ( ev, newEv ) <- eigenVariables( et, originalSh )
    } yield ( ev, newEv ) )
    ExpansionProof( for {
      et <- expansionProof.expansionSequent
      originalSh <- endSequent.elements
      if forward( originalSh, Map[Var, FOLVar]() ) == et.shallow
    } yield back( et, originalSh, evs ) )
  }

  def back( t: FOLTerm, freeVars: Map[FOLVar, Var] ): Expr = t match {
    case v: FOLVar                         => freeVars( v )
    case Apps( c: FOLFunctionConst, args ) => termReification( c )( args map { _.asInstanceOf[FOLTerm] } map { back( _, freeVars ) }: _* )
  }

  def back( formula: FOLFormula, freeVars: Map[FOLVar, Var] ): Formula = formula match {
    case f @ Top()    => f
    case f @ Bottom() => f
    case Neg( f )     => Neg( back( f, freeVars ) )
    case And( a, b )  => And( back( a, freeVars ), back( b, freeVars ) )
    case Or( a, b )   => Or( back( a, freeVars ), back( b, freeVars ) )
    case Eq( a, b )   => Eq( back( a, freeVars ), back( b, freeVars ) )
    case Apps( c: FOLAtomConst, args ) =>
      predicateReification( c )( args map { _.asInstanceOf[FOLTerm] } map { back( _, freeVars ) }: _* )
  }

  def back( atom: FOLAtom, freeVars: Map[FOLVar, Var] ): Atom =
    back( atom: FOLFormula, freeVars ).asInstanceOf[Atom]
}

/**
 * Reduces finding a resolution proof of a many-sorted clause set to the first-order case.
 *
 * Sorts are simply ignored and we make a best effort to convert the resolution refutation back.
 */
case object ErasureReductionCNF extends Reduction_[Set[HOLClause], ResolutionProof] {
  override def forward( problem: Set[HOLClause] ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    val helper = new ErasureReductionHelper( problem flatMap { constants( _ ) } )
    ( problem map helper.forward, helper.back( _, problem ) )
  }
}

/**
 * Reduces finding an expansion proof of a many-sorted sequent to the first-order case.
 *
 * Sorts are simply ignored and we make a best effort to convert the expansion tree.
 */
case object ErasureReductionET extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val helper = new ErasureReductionHelper( constants( problem ) )
    ( helper.forward( problem ), helper.back( _, problem ) )
  }
}

private class PredicateReductionHelper( constants: Set[Const] ) {
  private val nameGen = rename awayFrom constants

  val baseTypes = constants flatMap { case Const( _, FunctionType( ret, args ), _ ) => ret +: args }
  val predicateForType = baseTypes.map { ty => ty -> HOLAtomConst( nameGen fresh s"is_$ty", ty ) }.toMap
  val predicates = predicateForType.values.toSet

  val predicateAxioms = constants.map {
    case c @ Const( _, FunctionType( retType, argTypes ), _ ) =>
      val args = argTypes.zipWithIndex map { case ( t, i ) => Var( s"x$i", t ) }
      And( args map { a => predicateForType( a.ty )( a ) } ) --> predicateForType( retType )( c( args: _* ) )
  }

  val nonEmptyWitnesses = baseTypes.map { ty => Const( nameGen fresh s"nonempty_$ty", ty ) }
  val nonEmptyAxioms = nonEmptyWitnesses.map { w => predicateForType( w.ty )( w ) }

  val extraAxioms = existentialClosure( predicateAxioms ++: nonEmptyAxioms ++: Sequent() )
  val extraAxiomClauses = CNFn( extraAxioms.toDisjunction )

  private def guard( formula: Formula ): Formula = formula match {
    case Top() | Bottom() | Atom( _, _ ) => formula
    case Neg( f )                        => Neg( guard( f ) )
    case And( f, g )                     => And( guard( f ), guard( g ) )
    case Or( f, g )                      => Or( guard( f ), guard( g ) )
    case Imp( f, g )                     => Imp( guard( f ), guard( g ) )
    case All( x @ Var( _, t ), f )       => All( x, predicateForType( t )( x ) --> guard( f ) )
    case Ex( x @ Var( _, t ), f )        => Ex( x, predicateForType( t )( x ) & guard( f ) )
  }

  private def guardAndAddAxioms( sequent: HOLSequent ): HOLSequent =
    extraAxioms ++ sequent.map( guard )

  def forward( sequent: HOLSequent ): HOLSequent =
    guardAndAddAxioms( sequent )

  def forward( cnf: Set[HOLClause] ): Set[HOLClause] =
    extraAxiomClauses union cnf.map( forward )
  def forward( clause: HOLClause )( implicit dummyImplicit: DummyImplicit ): HOLClause =
    CNFp( guard( universalClosure( clause.toImplication ) ) ).head

  def back( proof: ResolutionProof ): ResolutionProof =
    mapInputClauses( proof ) { cls =>
      val clauseWithoutPredicates = cls filterNot { case Apps( c: HOLAtomConst, _ ) => predicates contains c }
      if ( clauseWithoutPredicates.nonEmpty )
        Input( clauseWithoutPredicates )
      else
        Input( cls )
    }

  def unguard( formula: Formula ): Formula = formula match {
    case Top() | Bottom() | Atom( _, _ ) => formula
    case Neg( f )                        => Neg( unguard( f ) )
    case And( f, g )                     => And( unguard( f ), unguard( g ) )
    case Or( f, g )                      => Or( unguard( f ), unguard( g ) )
    case Imp( f, g )                     => Imp( unguard( f ), unguard( g ) )
    case All( x, Imp( grd, f ) )         => All( x, unguard( f ) )
    case Ex( x, And( grd, f ) )          => Ex( x, unguard( f ) )
  }
  def unguard( et: ExpansionTree ): ExpansionTree = et match {
    case ETMerge( a, b )        => ETMerge( unguard( a ), unguard( b ) )
    case ETWeakening( f, pol )  => ETWeakening( unguard( f ), pol )
    case _: ETAtom              => et
    case _: ETTop | _: ETBottom => et
    case ETNeg( a )             => ETNeg( unguard( a ) )
    case ETAnd( a, b )          => ETAnd( unguard( a ), unguard( b ) )
    case ETOr( a, b )           => ETOr( unguard( a ), unguard( b ) )
    case ETImp( a, b )          => ETImp( unguard( a ), unguard( b ) )
    case ETWeakQuantifier( shallow, insts ) =>
      ETWeakQuantifier(
        unguard( shallow ),
        insts map {
          case ( t, ETImp( _, inst ) ) if et.polarity.inAnt => t -> unguard( inst )
          case ( t, ETAnd( _, inst ) ) if et.polarity.inSuc => t -> unguard( inst )
        } )
    case ETDefinition( _, _ ) | ETSkolemQuantifier( _, _, _, _ ) | ETStrongQuantifier( _, _, _ ) => throw new IllegalArgumentException
  }

  def back( expansionProof: ExpansionProof, endSequent: HOLSequent ): ExpansionProof =
    ExpansionProof( expansionProof.expansionSequent.zipWithIndex collect {
      case ( et, i ) if !extraAxioms.contains( et.shallow, i.polarity ) =>
        unguard( et )
    } )
}

/**
 * Simplifies the problem of finding a resolution refutation of a many-sorted clause set by adding
 * predicates for each of the sorts.  The resulting problem is still many-sorted.
 */
case object PredicateReductionCNF extends Reduction_[Set[HOLClause], ResolutionProof] {
  override def forward( problem: Set[HOLClause] ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    val helper = new PredicateReductionHelper( problem flatMap { constants( _ ) } )
    ( helper forward problem, helper.back )
  }
}

/**
 * Simplifies the problem of finding an expansion proof of a many-sorted sequent by adding
 * predicates for each of the sorts.  The resulting problem is still many-sorted.
 */
case object PredicateReductionET extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val helper = new PredicateReductionHelper( constants( problem ) )
    ( helper.forward( problem ), helper.back( _, problem ) )
  }
}

private object removeReflsAndTauts {
  def apply( proof: ResolutionProof ): ResolutionProof =
    new ResolutionProofVisitor {
      override def apply( p: ResolutionProof ): ResolutionProof = {
        for {
          Eq( t, t_ ) <- p.conclusion.succedent
          if t == t_
        } return Refl( t )
        if ( p.conclusion.isTaut )
          return Taut( p.conclusion.antecedent intersect p.conclusion.succedent head )
        super.apply( p )
      }
    }.apply( proof )
}

private object definitionIntroducingBackReplacement {
  def apply( proof: ResolutionProof, defs: Map[Const, Expr] ): ResolutionProof = {
    val nonBoolReplaced = TermReplacement( proof, defs.filterNot { _._1.isInstanceOf[HOLAtomConst] }.toMap )
    new ResolutionProofVisitor {
      override def apply( p: ResolutionProof ): ResolutionProof =
        p.conclusion match {
          case Sequent( Seq(), Seq( Eq( t, t_ ) ) ) if t == t_ =>
            Refl( t )
          case Sequent( Seq(), Seq( Iff( f @ Apps( c: HOLAtomConst, args ), g ) ) ) if defs.contains( c ) =>
            var defn: ResolutionProof = Defn( c, defs( c ) )
            for ( ev <- args ) defn = AllR( defn, Suc( 0 ), ev.asInstanceOf[Var] )
            defn
          case _ => super.apply( p )
        }
    }.apply( nonBoolReplaced )
  }
}

private class LambdaEliminationReductionHelper( constants: Set[Const], lambdas: Set[Abs], addAxioms: Boolean ) {
  val nameGen = rename.awayFrom( constants )

  private val replacements = mutable.Map[Abs, Expr]()
  private val extraAxioms = mutable.Buffer[Formula]()

  def equalOrEquivalent( a: Expr, b: Expr ) =
    if ( a.ty == To ) a <-> b else a === b

  private def setup( e: Expr ): Expr = e match {
    case App( a, b )                           => App( setup( a ), setup( b ) )
    case v: Var                                => v
    case c: Const                              => c
    case lam: Abs if replacements contains lam => replacements( lam )
    case lam @ Abs( x, t ) =>
      val fvs = freeVariables( lam ).toSeq
      val lamSym = Const( nameGen freshWithIndex "lambda", FunctionType( lam.ty, fvs.map {
        _.ty
      } ) )
      replacements( lam ) = lamSym( fvs: _* )
      extraAxioms += universalClosure( equalOrEquivalent( replacements( lam )( x ), t ) )
      replacements( lam )
  }

  private def setup( f: Formula ): Formula = f match {
    case All( x, g )      => All( x, setup( g ) )
    case Ex( x, g )       => Ex( x, setup( g ) )
    case Top() | Bottom() => f
    case Neg( g )         => Neg( setup( g ) )
    case And( g, h )      => And( setup( g ), setup( h ) )
    case Or( g, h )       => Or( setup( g ), setup( h ) )
    case Imp( g, h )      => Imp( setup( g ), setup( h ) )
    case Apps( hd, args ) => hd( args map setup: _* ).asInstanceOf[Formula]
  }

  lambdas foreach setup
  if ( !addAxioms ) extraAxioms.clear()
  val extraAxiomClauses = extraAxioms.flatMap { case All.Block( vs, f ) => Seq( Seq() :- Seq( f ) ) }

  def delambdaify( e: Expr ): Expr = e match {
    case App( a, b )       => App( delambdaify( a ), delambdaify( b ) )
    case lam: Abs          => replacements( lam )
    case _: Var | _: Const => e
  }

  def delambdaify( f: Formula ): Formula = f match {
    case All( x, g )      => All( x, delambdaify( g ) )
    case Ex( x, g )       => Ex( x, delambdaify( g ) )
    case Top() | Bottom() => f
    case Neg( g )         => Neg( delambdaify( g ) )
    case And( g, h )      => And( delambdaify( g ), delambdaify( h ) )
    case Or( g, h )       => Or( delambdaify( g ), delambdaify( h ) )
    case Imp( g, h )      => Imp( delambdaify( g ), delambdaify( h ) )
    case Apps( hd, args ) => hd( args map delambdaify: _* ).asInstanceOf[Formula]
  }

  def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent map delambdaify

  def forward( cnf: Set[HOLSequent] ): Set[HOLSequent] =
    cnf.map( _.map( delambdaify ).map( _.asInstanceOf[Atom] ) ) ++ extraAxiomClauses

  val backReplacements = replacements.
    map { case ( abs, Apps( c: Const, args ) ) => c -> Abs( args.map( _.asInstanceOf[Var] ), abs ) }

  def back( expansion: ExpansionProof ): ExpansionProof =
    ExpansionProof( TermReplacement(
      expansion.expansionSequent.filterNot { e => extraAxioms.contains( e.shallow ) },
      { case expr => BetaReduction.betaNormalize( TermReplacement( expr, backReplacements.toMap ) ) } ) )

  def back( resolution: ResolutionProof ): ResolutionProof =
    definitionIntroducingBackReplacement( resolution, backReplacements.toMap )
}

/**
 * Replaces lambda abstractions by fresh function symbols, together with axioms that axiomatize them.
 */
case class LambdaEliminationReduction( extraAxioms: Boolean = true ) extends OneWayReduction_[HOLSequent] {
  override def forward( problem: HOLSequent ) = {
    val lambdas = atoms( problem ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }.toSet
    val helper = new LambdaEliminationReductionHelper( constants( problem ), lambdas, extraAxioms )
    ( helper.forward( problem ), _ => throw new UnsupportedOperationException )
  }
}

/**
 * Replaces lambda abstractions by fresh function symbols, together with axioms that axiomatize them.
 */
case class LambdaEliminationReductionET( extraAxioms: Boolean = true ) extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val lambdas = atoms( problem ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }
    val helper = new LambdaEliminationReductionHelper( constants( problem ), lambdas, extraAxioms )
    ( helper.forward( problem ), helper.back( _ ) )
  }
}

/**
 * Replaces lambda abstractions by fresh function symbols, together with axioms that axiomatize them.
 */
case class LambdaEliminationReductionRes( extraAxioms: Boolean = true ) extends Reduction_[HOLSequent, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ResolutionProof ) => ResolutionProof ) = {
    val lambdas = atoms( problem ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }
    val helper = new LambdaEliminationReductionHelper( constants( problem ), lambdas, extraAxioms )
    ( helper.forward( problem ), helper.back( _ ) )
  }
}

/**
 * Replaces lambda abstractions by fresh function symbols, together with axioms that axiomatize them.
 */
case class LambdaEliminationReductionCNFRes( extraAxioms: Boolean = true ) extends Reduction_[Set[HOLSequent], ResolutionProof] {
  override def forward( problem: Set[HOLSequent] ): ( Set[HOLSequent], ( ResolutionProof ) => ResolutionProof ) = {
    val lambdas = problem.flatMap( atoms( _ ) ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }
    val helper = new LambdaEliminationReductionHelper( problem.flatMap( constants( _ ) ), lambdas, extraAxioms )
    ( helper.forward( problem ), helper.back )
  }
}

private class HOFunctionReductionHelper( names: Set[VarOrConst], addExtraAxioms: Boolean ) {
  private val nameGen = rename.awayFrom( names )
  val baseTys = names map { _.ty } flatMap { baseTypes( _ ) }
  private val typeNameGen = new NameGenerator( baseTys.map { _.name } )

  val partialAppTypes = names map { _.ty } flatMap {
    case FunctionType( _, argTypes ) =>
      argTypes.filterNot { _.isInstanceOf[TBase] }
  } map { t => ( TBase( typeNameGen freshWithIndex "fun" ), t ) } toMap

  def equalOrEquivalent( a: Expr, b: Expr ) =
    if ( a.ty == To ) a <-> b else a === b

  val partiallyAppedTypes = partialAppTypes.map { _.swap }

  val applyFunctions = partialAppTypes.map {
    case ( partialAppType, ty @ FunctionType( ret, args ) ) =>
      partialAppType -> Const( nameGen freshWithIndex "apply", partialAppType ->: ty )
  }

  val partialApplicationFuns =
    for {
      ( partialAppType, funType @ FunctionType( ret, argTypes ) ) <- partialAppTypes
      g @ Const( _, FunctionType( `ret`, gArgTypes ), _ ) <- names
      if gArgTypes endsWith argTypes
    } yield ( Const(
      nameGen freshWithIndex "partial",
      FunctionType( partialAppType, gArgTypes.dropRight( argTypes.size ) map reduceArgTy ) ), g, funType )

  val newConstants = names.collect {
    case c @ Const( n, t, ps ) => c -> Const( n, reduceFunTy( t ), ps.map( reduceFunTy ) )
  }.toMap

  val extraAxioms = if ( !addExtraAxioms ) Set() else
    for {
      f @ Const( _, FunctionType( ret, ( partialAppType: TBase ) :: argTypes ), _ ) <- applyFunctions.values
      ( partialApplicationFun @ Const( _, FunctionType( `partialAppType`, pappArgTypes ), _ ), g, _ ) <- partialApplicationFuns
    } yield {
      val varGen = rename.awayFrom( Set[Var]() )
      val gArgVars = pappArgTypes map { Var( varGen freshWithIndex "x", _ ) }
      val fArgVars = argTypes map { Var( varGen freshWithIndex "y", _ ) }
      universalClosure( equalOrEquivalent(
        applyFunctions( partialAppType )( partialApplicationFun( gArgVars: _* ) )( fArgVars: _* ),
        newConstants( g )( gArgVars: _* )( fArgVars: _* ) ) )
    }
  val extraAxiomClauses = extraAxioms.flatMap { case All.Block( vs, f ) => Seq( Seq() :- Seq( f ) ) }

  def reduceFunTy( t: Ty ): Ty = {
    val FunctionType( ret, args ) = t
    FunctionType( ret, args map reduceArgTy )
  }
  def reduceArgTy( t: Ty ): TBase = t match {
    case t: TBase => t
    case _        => partiallyAppedTypes( t )
  }

  def reduce( f: Formula ): Formula = reduce( f: Expr ).asInstanceOf[Formula]
  def reduce( e: Expr ): Expr = e match {
    case All( Var( x, t ), f ) => All( Var( x, reduceArgTy( t ) ), reduce( f ) )
    case Ex( Var( x, t ), f )  => Ex( Var( x, reduceArgTy( t ) ), reduce( f ) )
    case Top() | Bottom()      => e
    case Neg( f )              => Neg( reduce( f ) )
    case And( g, h )           => And( reduce( g ), reduce( h ) )
    case Or( g, h )            => Or( reduce( g ), reduce( h ) )
    case Imp( g, h )           => Imp( reduce( g ), reduce( h ) )

    case Var( n, t )           => Var( n, reduceArgTy( t ) )
    case Apps( f: Const, args ) if partiallyAppedTypes.contains( e.ty ) =>
      val Some( ( p, _, _ ) ) = partialApplicationFuns find { paf => paf._2 == f && paf._3 == e.ty }
      p( args map reduce: _* )
    case Apps( f: Var, args ) =>
      applyFunctions( reduceArgTy( f.ty ) )( reduce( f ) )( args map reduce: _* )
    case Apps( f: Const, args ) =>
      newConstants( f )( args map reduce: _* )
    //    case Abs( Var( x, t ), b ) => Abs( Var( x, reduceArgTy( t ) ), reduce( b ) )
  }

  def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent.map( reduce )

  def forward( cnf: Set[HOLSequent] ): Set[HOLSequent] =
    extraAxiomClauses.toSet ++ cnf.map( _.map( reduce ) )

  def back( formula: Formula ): Formula = back( formula: Expr ).asInstanceOf[Formula]
  def back( expr: Expr ): Expr = expr match {
    case Top() | Bottom() => expr
    case Neg( f )         => Neg( back( f ) )
    case And( f, g )      => And( back( f ), back( g ) )
    case Or( f, g )       => Or( back( f ), back( g ) )
    case Imp( f, g )      => Imp( back( f ), back( g ) )
    case All( x, f )      => All( back( x ).asInstanceOf[Var], back( f ) )
    case Ex( x, f )       => Ex( back( x ).asInstanceOf[Var], back( f ) )
    case Eq( a, b )       => Eq( back( a ), back( b ) )

    case Apps( f, args ) if partialApplicationFuns.exists { _._1 == f } =>
      partialApplicationFuns.find { _._1 == f }.get._2( args.map( back ) )
    case Apps( app, Seq( f, args @ _* ) ) if applyFunctions.exists { _._2 == app } =>
      back( f )( args.map( back ) )
    case Apps( f: Const, args ) => newConstants.map( _.swap ).getOrElse( f, f )( args map back )

    case Var( n, t: TBase )     => Var( n, partiallyAppedTypes.map( _.swap ).getOrElse( t, t ) )

    case Abs( v, f )            => Abs( back( v ).asInstanceOf[Var], back( f ) )
  }

  def back( et: ExpansionTree ): ExpansionTree = et match {
    case ETMerge( a, b )        => ETMerge( back( a ), back( b ) )
    case ETWeakening( f, pol )  => ETWeakening( back( f ), pol )
    case ETAtom( atom, pol )    => ETAtom( back( atom ).asInstanceOf[Atom], pol )
    case _: ETTop | _: ETBottom => et
    case ETNeg( a )             => ETNeg( back( a ) )
    case ETAnd( a, b )          => ETAnd( back( a ), back( b ) )
    case ETOr( a, b )           => ETOr( back( a ), back( b ) )
    case ETImp( a, b )          => ETImp( back( a ), back( b ) )
    case ETWeakQuantifier( shallow, insts ) =>
      ETWeakQuantifier(
        back( shallow ),
        for ( ( t, c ) <- insts ) yield back( t ) -> back( c ) )
    case ETDefinition( _, _ ) | ETSkolemQuantifier( _, _, _, _ ) | ETStrongQuantifier( _, _, _ ) => throw new IllegalArgumentException
  }

  def back( expansionProof: ExpansionProof ): ExpansionProof =
    ExpansionProof( expansionProof.expansionSequent.zipWithIndex collect {
      case ( et, i ) if !( i.isAnt && extraAxioms.toSeq.contains( et.shallow ) ) =>
        back( et )
    } )

  def back( resolutionProof: ResolutionProof ): ResolutionProof =
    removeReflsAndTauts( TermReplacement( resolutionProof, { case expr => back( expr ) } ) )
}

/**
 * Replaces the use of higher-order functions by fresh function symbols, together with axioms that axiomatize them.
 */
case class HOFunctionReduction( extraAxioms: Boolean = true ) extends OneWayReduction_[HOLSequent] {
  override def forward( problem: HOLSequent ) = {
    val helper = new HOFunctionReductionHelper( containedNames( problem ), extraAxioms )
    ( helper.forward( problem ), _ => throw new UnsupportedOperationException )
  }
}

/**
 * Replaces the use of higher-order functions by fresh function symbols, together with axioms that axiomatize them.
 */
case class HOFunctionReductionET( extraAxioms: Boolean = true ) extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ) = {
    val helper = new HOFunctionReductionHelper( containedNames( problem ), extraAxioms )
    ( helper.forward( problem ), helper.back( _ ) )
  }
}

/**
 * Replaces the use of higher-order functions by fresh function symbols, together with axioms that axiomatize them.
 */
case class HOFunctionReductionRes( extraAxioms: Boolean = true ) extends Reduction_[HOLSequent, ResolutionProof] {
  override def forward( problem: HOLSequent ) = {
    val helper = new HOFunctionReductionHelper( containedNames( problem ), extraAxioms )
    ( helper.forward( problem ), helper.back( _ ) )
  }
}

/**
 * Replaces the use of higher-order functions by fresh function symbols, together with axioms that axiomatize them.
 */
case class HOFunctionReductionCNFRes( extraAxioms: Boolean = true ) extends Reduction_[Set[HOLSequent], ResolutionProof] {
  override def forward( problem: Set[HOLSequent] ) = {
    val helper = new HOFunctionReductionHelper( containedNames( problem ), extraAxioms )
    ( helper.forward( problem ), helper.back )
  }
}

/**
 * Reduces finding an expansion proof for a sequent to finding a resolution proof of a clause set.
 */
case object CNFReductionExpRes extends Reduction[HOLSequent, Set[HOLClause], ExpansionProof, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( Set[HOLClause], ( ResolutionProof ) => ExpansionProof ) = {
    val cnf = structuralCNF( problem, propositional = false )
    ( cnf.map( _.conclusion.map( _.asInstanceOf[Atom] ) ),
      res => ResolutionToExpansionProof( mapInputClauses( res )( seq => cnf.find( _.conclusion == seq ).get ) ) )
  }
}

/**
 * Reduces finding an LK proof for a sequent to finding a resolution proof of a clause set.
 */
case object CNFReductionLKRes extends Reduction[HOLSequent, Set[HOLClause], LKProof, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( Set[HOLClause], ( ResolutionProof ) => LKProof ) = {
    val cnf = structuralCNF( problem, propositional = false )
    ( cnf.map( _.conclusion.map( _.asInstanceOf[Atom] ) ),
      res => ResolutionToLKProof( mapInputClauses( res )( seq => cnf.find( _.conclusion == seq ).get ) ) )
  }
}

/**
 * Reduces finding a resolution proof for a sequent to finding a resolution proof of a clause set.
 */
case object CNFReductionResRes extends Reduction[HOLSequent, Set[HOLClause], ResolutionProof, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    val cnf = structuralCNF( problem, propositional = false, structural = false /* FIXME */ )
    (
      cnf.map( _.conclusion.map( _.asInstanceOf[Atom] ) ),
      fixDerivation( _, cnf ) )
  }
}

/**
 * Reduces finding a resolution proof for a sequent set to finding a resolution proof of a clause set.
 */
case object CNFReductionSequentsResRes extends Reduction[Set[HOLSequent], Set[HOLClause], ResolutionProof, ResolutionProof] {
  override def forward( problem: Set[HOLSequent] ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    implicit val ctx = MutableContext.guess( problem ) // TODO(gabriel)
    val clausifier = new Clausifier( propositional = false, structural = false, bidirectionalDefs = false, cse = false,
      ctx = ctx, nameGen = ctx.newNameGenerator )
    problem.map( Input ).foreach( clausifier.expand )
    (
      Set() ++ clausifier.cnf.view.map( _.conclusion.map( _.asInstanceOf[Atom] ) ),
      fixDerivation( _, clausifier.cnf ) )
  }
}

/**
 * Simplifies the problem by grounding free variables.
 */
case object GroundingReductionET extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val nameGen = rename.awayFrom( constants( problem ) )
    val subst = for ( v @ Var( name, ty ) <- freeVariables( problem ) ) yield v -> Const( nameGen fresh name, ty )
    ( Substitution( subst )( problem ), exp => {
      require( exp.eigenVariables intersect subst.map( _._1 ) isEmpty )
      TermReplacement( exp, subst.map( _.swap ).toMap )
    } )
  }
}
