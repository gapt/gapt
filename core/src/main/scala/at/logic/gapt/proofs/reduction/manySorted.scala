package at.logic.gapt.proofs.reduction

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existsclosure, CNFn }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.ExpansionSequent
import at.logic.gapt.proofs.resolution.{ InputClause, mapInputClauses, ResolutionProof }

import scala.collection.mutable

trait FOLReduction {
  def forward( clause: HOLSequent ): FOLSequent

  def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof
  def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent
}

case class ErasureReduction( ctx: FiniteContext ) extends FOLReduction {
  val termErasure = ctx.constants map {
    case c @ Const( name, FunctionType( _, argTypes ) ) =>
      c -> FOLFunctionConst( s"f_$name", argTypes.size )
  } toMap
  val termReification = termErasure map { _.swap }

  val predicateErasure = ctx.constants collect {
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
      val y = rename( FOLVar( x.name ), freeVars.values.toList )
      All( y, forward( f, freeVars + ( x -> y ) ) )
    case Ex( x, f ) =>
      val y = rename( FOLVar( x.name ), freeVars.values.toList )
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

case class PredicateReduction( ctx: FiniteContext ) extends FOLReduction {
  val baseTypes = ctx.constants flatMap { case Const( _, FunctionType( ret, args ) ) => ret +: args }
  val predicateForType = baseTypes.map { ty => ty -> HOLAtomConst( s"is_$ty", ty ) }.toMap
  val predicates = predicateForType.values.toSet

  val intermediateContext = ctx ++ predicates
  val erasureReduction = ErasureReduction( intermediateContext )

  def reducedContext = erasureReduction.reducedContext

  val predicateAxioms = existsclosure( ctx.constants.map {
    case c @ Const( _, FunctionType( retType, argTypes ) ) =>
      val args = argTypes.zipWithIndex map { case ( t, i ) => Var( s"x$i", t ) }
      And( args map { a => predicateForType( a.exptype )( a ) } ) --> predicateForType( retType )( c( args: _* ) )
  } ++: Sequent() )

  val predicateAxiomClauses = CNFn.toFClauseList( predicateAxioms.toFormula ).toSet

  private def guard( formula: HOLFormula ): HOLFormula = formula match {
    case Top() | Bottom() | HOLAtom( _, _ ) => formula
    case Neg( f )                           => Neg( guard( formula ) )
    case And( f, g )                        => And( guard( f ), guard( g ) )
    case Or( f, g )                         => Or( guard( f ), guard( g ) )
    case Imp( f, g )                        => Imp( guard( f ), guard( g ) )
    case All( x @ Var( _, t ), f )          => All( x, predicateForType( t )( x ) --> guard( f ) )
    case Ex( x @ Var( _, t ), f )           => Ex( x, predicateForType( t )( x ) & guard( f ) )
  }

  private def guardAndAddAxioms( sequent: HOLSequent ): HOLSequent =
    predicateAxioms ++ sequent.map( guard )

  override def forward( sequent: HOLSequent ): FOLSequent =
    erasureReduction.forward( guardAndAddAxioms( sequent ) )

  override def back( proof: ResolutionProof, endSequent: HOLSequent ): ResolutionProof =
    mapInputClauses( erasureReduction.back( proof, guardAndAddAxioms( endSequent ) ) ) { cls =>
      val clauseWithoutPredicates = cls filterNot { case Apps( c: HOLAtomConst, _ ) => predicates contains c }
      if ( clauseWithoutPredicates.nonEmpty )
        InputClause( clauseWithoutPredicates )
      else
        InputClause( cls )
    }

  override def back( expansionSequent: ExpansionSequent, endSequent: HOLSequent ): ExpansionSequent = ???
}