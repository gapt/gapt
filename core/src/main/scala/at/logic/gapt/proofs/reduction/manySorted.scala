package at.logic.gapt.proofs.reduction

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ atoms, univclosure, existsclosure, CNFn }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.ExpansionSequent
import at.logic.gapt.proofs.resolution.{ InputClause, mapInputClauses, ResolutionProof }
import at.logic.gapt.utils.NameGenerator

import scala.collection.mutable

trait HOLReduction { self =>
  def context: FiniteContext
  def reducedContext: FiniteContext

  def forward( sequent: HOLSequent ): HOLSequent

  def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof
  def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent

  def |>( otherReduction: FiniteContext => HOLReduction ): HOLReduction =
    new HOLReduction {
      val other = otherReduction( self.reducedContext )

      def context = self.context
      def reducedContext = other.reducedContext

      def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof =
        self.back( other.back( proof, self.forward( endSequent ) ), endSequent )

      def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent =
        self.back( other.back( expansionSequent, self.forward( endSequent ) ), endSequent )

      def forward( sequent: HOLSequent ): HOLSequent =
        other.forward( self.forward( sequent ) )

      override def toString = s"$self |> $other"
    }
}

case class ErasureReduction( context: FiniteContext ) extends HOLReduction {
  val termErasure = context.constants map {
    case c @ Const( name, FunctionType( _, argTypes ) ) =>
      c -> FOLFunctionConst( s"f_$name", argTypes.size )
  } toMap
  val termReification = termErasure map { _.swap }

  val predicateErasure = context.constants collect {
    case c @ HOLAtomConst( name, argTypes ) =>
      c -> FOLAtomConst( s"P_$name", argTypes.size )
  } toMap
  val predicateReification = predicateErasure map { _.swap }

  val reducedContext = FiniteContext() +
    Context.Sort( "i" ) ++
    termErasure.values ++
    predicateErasure.values

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

  def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof =
    back( proof, CNFn.toFClauseList( endSequent.toFormula ).toSet )

  def back( proof: ResolutionProof, originalInputClauses: Set[HOLClause] ): ResolutionProof = {
    import at.logic.gapt.proofs.resolution._

    val memo = mutable.Map[( ResolutionProof, Map[FOLVar, Var] ), ResolutionProof]()

    def f( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = {
      g( p, freeVariables( p.conclusion ) map { case v: FOLVar => v -> vars( v ) } toMap )
    }

    def g( p: ResolutionProof, vars: Map[FOLVar, Var] ): ResolutionProof = memo.getOrElseUpdate( ( p, vars ), p match {
      case ReflexivityClause( term: FOLTerm ) => ReflexivityClause( back( term, vars ) )
      case TautologyClause( atom: FOLAtom )   => TautologyClause( back( atom, vars ).asInstanceOf[HOLAtom] )
      case InputClause( clause ) =>
        ( for (
          original <- originalInputClauses;
          subst <- syntacticMatching( original.toFormula, back( clause.toFormula.asInstanceOf[FOLFormula], vars ) )
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

      case Splitting( p0, c1, p1, p2 ) =>
        val subProofVars = infer( p0.conclusion.map { _.asInstanceOf[FOLAtom] }, vars )
        Splitting(
          f( p0, subProofVars ),
          c1 map { a => back( a.asInstanceOf[FOLAtom], subProofVars ).asInstanceOf[HOLAtom] },
          f( p1, vars ), f( p2, vars )
        )
    } )

    f( proof, Map() )
  }

  override def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent = ???

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
}

case class PredicateReduction( context: FiniteContext ) extends HOLReduction {
  val baseTypes = context.constants flatMap { case Const( _, FunctionType( ret, args ) ) => ret +: args }
  val predicateForType = baseTypes.map { ty => ty -> HOLAtomConst( s"is_$ty", ty ) }.toMap
  val predicates = predicateForType.values.toSet

  val reducedContext = context ++ predicates

  val predicateAxioms = existsclosure( context.constants.map {
    case c @ Const( _, FunctionType( retType, argTypes ) ) =>
      val args = argTypes.zipWithIndex map { case ( t, i ) => Var( s"x$i", t ) }
      And( args map { a => predicateForType( a.exptype )( a ) } ) --> predicateForType( retType )( c( args: _* ) )
  } ++: Sequent() )

  val predicateAxiomClauses = CNFn.toFClauseList( predicateAxioms.toFormula ).toSet

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
    predicateAxioms ++ sequent.map( guard )

  override def forward( sequent: HOLSequent ): HOLSequent =
    guardAndAddAxioms( sequent )

  override def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof =
    mapInputClauses( proof ) { cls =>
      val clauseWithoutPredicates = cls filterNot { case Apps( c: HOLAtomConst, _ ) => predicates contains c }
      if ( clauseWithoutPredicates.nonEmpty )
        InputClause( clauseWithoutPredicates )
      else
        InputClause( cls )
    }

  override def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent = ???
}

case class LambdaEliminationReduction( context: FiniteContext, lambdas: Set[Abs] ) extends HOLReduction {
  val nameGen = rename.awayFrom( context.constants )

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

  val reducedContext = context ++ constants( replacements.values )

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

  override def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent map delambdaify

  override def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof = ???

  override def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent = ???
}

case class HOFunctionReduction( context: FiniteContext ) extends HOLReduction {
  private val nameGen = rename.awayFrom( context.constants )
  private val typeNameGen = new NameGenerator( context.typeDefs.map { _.ty.name } )

  val partialAppTypes = context.constants flatMap {
    case Const( _, FunctionType( _, argTypes ) ) =>
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
      g @ Const( _, FunctionType( `ret`, gArgTypes ) ) <- context.constants
      if gArgTypes endsWith argTypes
    } yield ( Const(
      nameGen freshWithIndex "partial",
      FunctionType( partialAppType, gArgTypes.dropRight( argTypes.size ) map reduceArgTy )
    ), g, funType )

  val newConstants = context.constants.map {
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

  val reducedContext = context.copy( constants = newConstants.values.toSet ) ++
    partialAppTypes.keys.map { Context.Sort( _ ) } ++
    applyFunctions.values ++
    partialApplicationFuns.map { _._1 }

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

  override def forward( sequent: HOLSequent ): HOLSequent = extraAxioms ++: sequent.map { reduce( _ ).asInstanceOf[HOLFormula] }

  override def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof = ???

  override def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent = ???
}

case class HOFunctionReduction2( context: FiniteContext )
