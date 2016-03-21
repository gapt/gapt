package at.logic.gapt.proofs.reduction

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

trait Reduction[-P1, +P2, +S1, -S2] {
  def forward( problem: P1 ): ( P2, S2 => S1 )

  def |>[P2_ >: P2, P3, S2_ <: S2, S3]( other: Reduction[P2_, P3, S2_, S3] ): Reduction[P1, P3, S1, S3] =
    CombinedReduction( this, other )
}

trait Reduction_[P, S] extends Reduction[P, P, S, S]
trait OneWayReduction_[P] extends Reduction[P, P, Nothing, Any]

case class CombinedReduction[-P1, P2, +P3, +S1, S2, -S3](
    red1: Reduction[P1, P2, S1, S2],
    red2: Reduction[P2, P3, S2, S3]
) extends Reduction[P1, P3, S1, S3] {
  override def toString = s"$red1 |> $red2"

  override def forward( problem: P1 ): ( P3, S3 => S1 ) = {
    val ( prob2, back1 ) = red1.forward( problem )
    val ( prob3, back2 ) = red2.forward( prob2 )
    ( prob3, sol3 => back1( back2( sol3 ) ) )
  }
}

private class ErasureReductionHelper( constants: Set[Const] ) {
  val termErasure = constants map {
    case c @ Const( name, FunctionType( _, argTypes ) ) =>
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

  def forward( formula: HOLFormula, freeVars: Map[Var, FOLVar] ): FOLFormula = formula match {
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

  def forward( term: LambdaExpression, freeVars: Map[Var, FOLVar] ): FOLTerm = term match {
    case Apps( c: Const, args ) =>
      termErasure( c )( args map { forward( _, freeVars ) }: _* )
    case v: Var => freeVars( v )
  }

  def infer( atom: FOLAtom, known: Map[FOLVar, Var] ): Map[FOLVar, Var] = {
    val res = mutable.Map[FOLVar, Var]()
    res ++= known

    def formula( f: FOLAtom ) = f match {
      case Eq( a @ FOLFunction( _, _ ), b ) =>
        term( b, term( a, null ) )
      case Eq( a, b @ FOLFunction( _, _ ) ) =>
        term( a, term( b, null ) )
      case Eq( a: FOLVar, b ) if known isDefinedAt a =>
        term( b, known( a ).exptype )
      case Eq( a, b: FOLVar ) if known isDefinedAt b =>
        term( b, known( b ).exptype )
      case Eq( a: FOLVar, b: FOLVar ) => term( b, term( a, Ti ) ) // hope for the best...
      case Apps( c: FOLAtomConst, args ) =>
        predicateReification( c ) match {
          case Const( _, FunctionType( _, argTypes ) ) =>
            for ( ( a: FOLTerm, t ) <- args zip argTypes )
              term( a, t )
        }
    }

    def term( f: FOLTerm, termType: Ty ): Ty = f match {
      case v @ FOLVar( name ) =>
        res.get( v ) match {
          case Some( Var( _, `termType` ) ) =>
          case Some( Var( _, other ) ) =>
            throw new Exception( s"Reification failure: $v should have type $termType but already has type $other instead" )
          case None => res( v ) = Var( name, termType )
        }
        termType
      case Apps( c: FOLFunctionConst, args ) =>
        termReification( c ) match {
          case Const( _, FunctionType( retType, argTypes ) ) =>
            for ( ( a: FOLTerm, t ) <- args zip argTypes )
              term( a, t )
            retType
        }
    }

    formula( atom )
    res.toMap
  }

  def infer( clause: FOLClause, known: Map[FOLVar, Var] ): Map[FOLVar, Var] =
    clause.elements.foldRight( known )( infer )

  def back( proof: ResolutionProof, originalInputClauses: Set[HOLClause] ): ResolutionProof = {
    import at.logic.gapt.proofs.resolution._

    val memo = mutable.Map[( ResolutionProof, Map[FOLVar, Var] ), ResolutionProof]()

    def f( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = {
      g( p, freeVariables( p.conclusion ) map { case v: FOLVar => v -> vars( v ) } toMap )
    }

    def g( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = memo.getOrElseUpdate( ( p, vars ), p match {
      case ReflexivityClause( term: FOLTerm ) => ReflexivityClause( back( term, vars ) )
      case TautologyClause( atom: FOLAtom )   => TautologyClause( back( atom, vars ) )
      case InputClause( clause ) =>
        ( for (
          original <- originalInputClauses;
          subst <- syntacticMatching( original.toDisjunction, back( clause.toDisjunction.asInstanceOf[FOLFormula], vars ) )
        ) yield Instance( InputClause( original ), subst ) ).head

      case Instance( subProof, subst ) =>
        val subProofVars = freeVariables( subProof.conclusion ).map {
          case v @ FOLVar( name ) =>
            v -> Var( name, subst( v ) match {
              case Apps( head: FOLFunctionConst, _ ) =>
                termReification( head ) match { case Const( _, FunctionType( retType, _ ) ) => retType }
              case u: FOLVar => vars( u ).exptype
            } )
        }.toMap
        val subProof_ = f( subProof, subProofVars )
        val newSubst = Substitution( freeVariables( subProof.conclusion ) map {
          case v @ FOLVar( name ) =>
            subProofVars( v ) -> back( subst( v ).asInstanceOf[FOLTerm], vars )
        } )
        Instance( subProof_, newSubst )

      case Factor( subProof, idx1, idx2 ) =>
        Factor( f( subProof, vars ), idx1, idx2 )

      case Resolution( subProof1, idx1, subProof2, idx2 ) =>
        val subProofVars = infer( subProof1.conclusion( idx1 ).asInstanceOf[FOLAtom], vars )
        val q1 = f( subProof1, subProofVars )
        val q2 = f( subProof2, subProofVars )
        Resolution( q1, idx1, q2, idx2 )

      case Paramodulation( subProof1, eq, subProof2, lit, pos, ltr ) =>
        val subProofVars = infer( subProof1.conclusion( eq ).asInstanceOf[FOLAtom], vars )
        val q1 = f( subProof1, subProofVars )
        val q2 = f( subProof2, subProofVars )
        Paramodulation( q1, eq, q2, lit, pos, ltr )

      case Splitting( p0, c1, c2, p1, p2 ) =>
        val subProofVars = infer( p0.conclusion.map { _.asInstanceOf[FOLAtom] }, vars )
        Splitting(
          f( p0, subProofVars ),
          c1 map { a => back( a.asInstanceOf[FOLAtom], subProofVars ) },
          c2 map { a => back( a.asInstanceOf[FOLAtom], subProofVars ) },
          f( p1, vars ), f( p2, vars )
        )
    } )

    f( proof, Map() )
  }

  def back( et: ExpansionTree, shallow: HOLFormula ): ExpansionTree = ( et, shallow ) match {
    case ( ETAtom( atom: FOLAtom, pol ), _ ) => ETAtom( back( atom, Map() ), pol )
    case ( ETWeakening( _, pol ), _ )        => ETWeakening( shallow, pol )
    case ( ETMerge( a, b ), _ )              => ETMerge( back( a, shallow ), back( b, shallow ) )
    case ( _: ETBottom | _: ETTop, _ )       => et
    case ( ETNeg( a ), Neg( sha ) )          => ETNeg( back( a, sha ) )
    case ( ETAnd( a, b ), And( sha, shb ) )  => ETAnd( back( a, sha ), back( b, shb ) )
    case ( ETOr( a, b ), Or( sha, shb ) )    => ETOr( back( a, sha ), back( b, shb ) )
    case ( ETImp( a, b ), Imp( sha, shb ) )  => ETImp( back( a, sha ), back( b, shb ) )
    case ( ETWeakQuantifier( _, insts ), Quant( x, sh ) ) =>
      ETWeakQuantifier(
        shallow,
        for ( ( t, inst ) <- insts ) yield {
          val t_ = back( t.asInstanceOf[FOLTerm], Map[FOLVar, Var]() )
          t_ -> back( inst, Substitution( x -> t_ )( sh ) )
        }
      )
  }

  def back( expansionProof: ExpansionProof, endSequent: HOLSequent ): ExpansionProof =
    ExpansionProof( expansionProof.expansionSequent zip endSequent map {
      case ( et, sh ) =>
        require( forward( sh, Map[Var, FOLVar]() ) == et.shallow )
        back( et, sh )
    } )

  def back( t: FOLTerm, freeVars: Map[FOLVar, Var] ): LambdaExpression = t match {
    case v: FOLVar                         => freeVars( v )
    case Apps( c: FOLFunctionConst, args ) => termReification( c )( args map { _.asInstanceOf[FOLTerm] } map { back( _, freeVars ) }: _* )
  }

  def back( formula: FOLFormula, freeVars: Map[FOLVar, Var] ): HOLFormula = formula match {
    case f @ Top()    => f
    case f @ Bottom() => f
    case Neg( f )     => Neg( back( f, freeVars ) )
    case And( a, b )  => And( back( a, freeVars ), back( b, freeVars ) )
    case Or( a, b )   => Or( back( a, freeVars ), back( b, freeVars ) )
    case Eq( a, b )   => Eq( back( a, freeVars ), back( b, freeVars ) )
    case Apps( c: FOLAtomConst, args ) =>
      predicateReification( c )( args map { _.asInstanceOf[FOLTerm] } map { back( _, freeVars ) }: _* )
  }

  def back( atom: FOLAtom, freeVars: Map[FOLVar, Var] ): HOLAtom =
    back( atom: FOLFormula, freeVars ).asInstanceOf[HOLAtom]
}

case object ErasureReductionCNF extends Reduction_[Set[HOLClause], ResolutionProof] {
  override def forward( problem: Set[HOLClause] ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    val helper = new ErasureReductionHelper( problem flatMap { constants( _ ) } )
    ( problem map helper.forward, helper.back( _, problem ) )
  }
}

case object ErasureReductionET extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val helper = new ErasureReductionHelper( constants( problem ) )
    ( helper.forward( problem ), helper.back( _, problem ) )
  }
}

private class PredicateReductionHelper( constants: Set[Const] ) {
  private val nameGen = rename awayFrom constants

  val baseTypes = constants flatMap { case Const( _, FunctionType( ret, args ) ) => ret +: args }
  val predicateForType = baseTypes.map { ty => ty -> HOLAtomConst( nameGen fresh s"is_$ty", ty ) }.toMap
  val predicates = predicateForType.values.toSet

  val predicateAxioms = constants.map {
    case c @ Const( _, FunctionType( retType, argTypes ) ) =>
      val args = argTypes.zipWithIndex map { case ( t, i ) => Var( s"x$i", t ) }
      And( args map { a => predicateForType( a.exptype )( a ) } ) --> predicateForType( retType )( c( args: _* ) )
  }

  val nonEmptyWitnesses = baseTypes.map { ty => Const( nameGen fresh s"nonempty_$ty", ty ) }
  val nonEmptyAxioms = nonEmptyWitnesses.map { w => predicateForType( w.exptype )( w ) }

  val extraAxioms = existsclosure( predicateAxioms ++: nonEmptyAxioms ++: Sequent() )
  val extraAxiomClauses = CNFn.toFClauseList( extraAxioms.toDisjunction ).toSet

  private def guard( formula: HOLFormula ): HOLFormula = formula match {
    case Top() | Bottom() | HOLAtom( _, _ ) => formula
    case Neg( f )                           => Neg( guard( f ) )
    case And( f, g )                        => And( guard( f ), guard( g ) )
    case Or( f, g )                         => Or( guard( f ), guard( g ) )
    case Imp( f, g )                        => Imp( guard( f ), guard( g ) )
    case All( x @ Var( _, t ), f )          => All( x, predicateForType( t )( x ) --> guard( f ) )
    case Ex( x @ Var( _, t ), f )           => Ex( x, predicateForType( t )( x ) & guard( f ) )
  }

  private def guardAndAddAxioms( sequent: HOLSequent ): HOLSequent =
    extraAxioms ++ sequent.map( guard )

  def forward( sequent: HOLSequent ): HOLSequent =
    guardAndAddAxioms( sequent )

  def forward( cnf: Set[HOLClause] ): Set[HOLClause] =
    extraAxiomClauses union cnf.map( forward )
  def forward( clause: HOLClause )( implicit dummyImplicit: DummyImplicit ): HOLClause =
    CNFp.toClauseList( guard( univclosure( clause.toImplication ) ) ).head

  def back( proof: ResolutionProof ): ResolutionProof =
    mapInputClauses( proof ) { cls =>
      val clauseWithoutPredicates = cls filterNot { case Apps( c: HOLAtomConst, _ ) => predicates contains c }
      if ( clauseWithoutPredicates.nonEmpty )
        InputClause( clauseWithoutPredicates )
      else
        InputClause( cls )
    }

  def unguard( formula: HOLFormula ): HOLFormula = formula match {
    case Top() | Bottom() | HOLAtom( _, _ ) => formula
    case Neg( f )                           => Neg( unguard( f ) )
    case And( f, g )                        => And( unguard( f ), unguard( g ) )
    case Or( f, g )                         => Or( unguard( f ), unguard( g ) )
    case Imp( f, g )                        => Imp( unguard( f ), unguard( g ) )
    case All( x, Imp( grd, f ) )            => All( x, unguard( f ) )
    case Ex( x, And( grd, f ) )             => Ex( x, unguard( f ) )
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
          case ( t, ETImp( _, inst ) ) if !et.polarity => t -> unguard( inst )
          case ( t, ETAnd( _, inst ) ) if et.polarity  => t -> unguard( inst )
        }
      )
  }

  def back( expansionProof: ExpansionProof, endSequent: HOLSequent ): ExpansionProof =
    ExpansionProof( expansionProof.expansionSequent.zipWithIndex collect {
      case ( et, i ) if !extraAxioms.contains( et.shallow, i.isSuc ) =>
        unguard( et )
    } )
}

case object PredicateReductionCNF extends Reduction_[Set[HOLClause], ResolutionProof] {
  override def forward( problem: Set[HOLClause] ): ( Set[HOLClause], ( ResolutionProof ) => ResolutionProof ) = {
    val helper = new PredicateReductionHelper( problem flatMap { constants( _ ) } )
    ( helper forward problem, helper.back )
  }
}

case object PredicateReductionET extends Reduction_[HOLSequent, ExpansionProof] {
  override def forward( problem: HOLSequent ): ( HOLSequent, ( ExpansionProof ) => ExpansionProof ) = {
    val helper = new PredicateReductionHelper( constants( problem ) )
    ( helper.forward( problem ), helper.back( _, problem ) )
  }
}

private class LambdaEliminationReductionHelper( constants: Set[Const], lambdas: Set[Abs] ) {
  val nameGen = rename.awayFrom( constants )

  private val replacements = mutable.Map[Abs, LambdaExpression]()
  private val extraAxioms = mutable.Buffer[HOLFormula]()

  private def setup( e: LambdaExpression ): LambdaExpression = e match {
    case App( a, b )                           => App( setup( a ), setup( b ) )
    case v: Var                                => v
    case c: Const                              => c
    case lam: Abs if replacements contains lam => replacements( lam )
    case lam @ Abs( x, t: HOLFormula ) =>
      val fvs = freeVariables( lam ).toSeq
      val lamSym = Const( nameGen freshWithIndex "lambda", FunctionType( lam.exptype, fvs.map {
        _.exptype
      } ) )
      replacements( lam ) = lamSym( fvs: _* )
      extraAxioms += univclosure( replacements( lam )( x ) <-> t )
      replacements( lam )
    case lam @ Abs( x, t ) =>
      val fvs = freeVariables( lam ).toSeq
      val lamSym = Const( nameGen freshWithIndex "lambda", FunctionType( lam.exptype, fvs.map {
        _.exptype
      } ) )
      replacements( lam ) = lamSym( fvs: _* )
      extraAxioms += univclosure( replacements( lam )( x ) === t )
      replacements( lam )
  }

  private def setup( f: HOLFormula ): HOLFormula = f match {
    case All( x, g )      => All( x, setup( g ) )
    case Ex( x, g )       => Ex( x, setup( g ) )
    case Top() | Bottom() => f
    case Neg( g )         => Neg( setup( g ) )
    case And( g, h )      => And( setup( g ), setup( h ) )
    case Or( g, h )       => Or( setup( g ), setup( h ) )
    case Imp( g, h )      => Imp( setup( g ), setup( h ) )
    case Apps( hd, args ) => hd( args map setup: _* ).asInstanceOf[HOLFormula]
  }

  lambdas foreach setup

  def delambdaify( e: LambdaExpression ): LambdaExpression = e match {
    case App( a, b )       => App( delambdaify( a ), delambdaify( b ) )
    case lam: Abs          => replacements( lam )
    case _: Var | _: Const => e
  }

  def delambdaify( f: HOLFormula ): HOLFormula = f match {
    case All( x, g )      => All( x, delambdaify( g ) )
    case Ex( x, g )       => Ex( x, delambdaify( g ) )
    case Top() | Bottom() => f
    case Neg( g )         => Neg( delambdaify( g ) )
    case And( g, h )      => And( delambdaify( g ), delambdaify( h ) )
    case Or( g, h )       => Or( delambdaify( g ), delambdaify( h ) )
    case Imp( g, h )      => Imp( delambdaify( g ), delambdaify( h ) )
    case Apps( hd, args ) => hd( args map delambdaify: _* ).asInstanceOf[HOLFormula]
  }

  def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent map delambdaify
}

case object LambdaEliminationReduction extends OneWayReduction_[HOLSequent] {
  override def forward( problem: HOLSequent ) = {
    val lambdas = atoms( problem ).flatMap { subTerms( _ ) }.collect { case a: Abs => a }.toSet
    val helper = new LambdaEliminationReductionHelper( constants( problem ), lambdas )
    ( helper.forward( problem ), _ => throw new UnsupportedOperationException )
  }
}

private class HOFunctionReductionHelper( constants: Set[Const], variables: Set[Var] ) {
  private val nameGen = rename.awayFrom( constants )
  val baseTys = ( Set[LambdaExpression]() ++ constants ++ variables ) map { _.exptype } flatMap { baseTypes( _ ) }
  private val typeNameGen = new NameGenerator( baseTys.map { _.name } )

  val partialAppTypes = ( Set[LambdaExpression]() ++ constants ++ variables ) map { _.exptype } flatMap {
    case FunctionType( _, argTypes ) =>
      argTypes.filterNot { _.isInstanceOf[TBase] }
  } map { t => ( TBase( typeNameGen freshWithIndex "fun" ), t ) } toMap

  val partiallyAppedTypes = partialAppTypes.map { _.swap }

  val applyFunctions = partialAppTypes.map {
    case ( partialAppType, ty @ FunctionType( ret, args ) ) =>
      partialAppType -> Const( nameGen freshWithIndex "apply", partialAppType -> ty )
  }

  val partialApplicationFuns =
    for {
      ( partialAppType, funType @ FunctionType( ret, argTypes ) ) <- partialAppTypes
      g @ Const( _, FunctionType( `ret`, gArgTypes ) ) <- constants
      if gArgTypes endsWith argTypes
    } yield ( Const(
      nameGen freshWithIndex "partial",
      FunctionType( partialAppType, gArgTypes.dropRight( argTypes.size ) map reduceArgTy )
    ), g, funType )

  val newConstants = constants.map {
    case c @ Const( n, t ) => c -> Const( n, reduceFunTy( t ) )
  }.toMap

  val extraAxioms =
    for {
      f @ Const( _, FunctionType( ret, ( partialAppType: TBase ) :: argTypes ) ) <- applyFunctions.values
      ( partialApplicationFun @ Const( _, FunctionType( `partialAppType`, pappArgTypes ) ), g, _ ) <- partialApplicationFuns
    } yield {
      val varGen = rename.awayFrom( Set[Var]() )
      val gArgVars = pappArgTypes map { Var( varGen freshWithIndex "x", _ ) }
      val fArgVars = argTypes map { Var( varGen freshWithIndex "y", _ ) }
      univclosure( applyFunctions( partialAppType )( partialApplicationFun( gArgVars: _* ) )( fArgVars: _* ) ===
        newConstants( g )( gArgVars: _* )( fArgVars: _* ) )
    }

  def reduceFunTy( t: Ty ): Ty = {
    val FunctionType( ret, args ) = t
    FunctionType( ret, args map reduceArgTy )
  }
  def reduceArgTy( t: Ty ): TBase = t match {
    case t: TBase => t
    case _        => partiallyAppedTypes( t )
  }

  def reduce( e: LambdaExpression ): LambdaExpression = e match {
    case All( Var( x, t ), f ) => All( Var( x, reduceArgTy( t ) ), reduce( f ) )
    case Ex( Var( x, t ), f )  => Ex( Var( x, reduceArgTy( t ) ), reduce( f ) )
    case Top() | Bottom()      => e
    case Neg( f )              => Neg( reduce( f ) )
    case And( g, h )           => And( reduce( g ), reduce( h ) )
    case Or( g, h )            => Or( reduce( g ), reduce( h ) )
    case Imp( g, h )           => Imp( reduce( g ), reduce( h ) )

    case Var( n, t )           => Var( n, reduceArgTy( t ) )
    case Apps( f: Const, args ) if partiallyAppedTypes.contains( e.exptype ) =>
      val Some( ( p, _, _ ) ) = partialApplicationFuns find { paf => paf._2 == f && paf._3 == e.exptype }
      p( args map reduce: _* )
    case Apps( f: Var, args ) =>
      applyFunctions( reduceArgTy( f.exptype ) )( reduce( f ) )( args map reduce: _* )
    case Apps( f: Const, args ) =>
      newConstants( f )( args map reduce: _* )
    //    case Abs( Var( x, t ), b ) => Abs( Var( x, reduceArgTy( t ) ), reduce( b ) )
  }

  def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent.map { reduce( _ ).asInstanceOf[HOLFormula] }
}

case object HOFunctionReduction extends OneWayReduction_[HOLSequent] {
  override def forward( problem: HOLSequent ) = {
    val helper = new HOFunctionReductionHelper( constants( problem ), variables( problem ) )
    ( helper.forward( problem ), _ => throw new UnsupportedOperationException )
  }
}

case object CNFReductionExpRes extends Reduction[HOLSequent, Set[HOLClause], ExpansionProof, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( Set[HOLClause], ( ResolutionProof ) => ExpansionProof ) = {
    val ( cnf, justs, defs ) = structuralCNF( problem, true, false )
    ( cnf, RobinsonToExpansionProof( _, problem, justs, defs ) )
  }
}

case object CNFReductionLKRes extends Reduction[HOLSequent, Set[HOLClause], LKProof, ResolutionProof] {
  override def forward( problem: HOLSequent ): ( Set[HOLClause], ( ResolutionProof ) => LKProof ) = {
    val ( cnf, justs, defs ) = structuralCNF( problem, true, false )
    ( cnf, RobinsonToLK( _, problem, justs, defs, addWeakenings = true ) )
  }
}
