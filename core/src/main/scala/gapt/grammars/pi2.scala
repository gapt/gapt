package gapt.grammars
import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Or
import gapt.expr.formula.fol.{ folSubTerms, thresholds }
import gapt.expr.formula.hol.{ lcomp, simplify, toNNF }
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.provers.maxsat.MaxSATSolver
import gapt.utils.Logger

/**
 * This is a slightly batshit insane and completely wrong formalization of grammars for proofs with a single Π₂-cut.
 * (Should be isomorphic to the usual versions though.)
 *
 * Say `∀x ∃y φ(x,y)` is the cut-formula.
 *
 * Then the left side of the cut has one strong quantifier inference (with eigenvariable α),
 * and many weak quantifier inferences (with terms `t`).  Each weak quantifier inference is stored as the
 * production `α → t` (yes, yes, and also, `t` may contain `α`).
 *
 * The right side of the cut has alternating weak and strong quantifier inferences.  Say `r` is the term of
 * the weak quantifier inference, then `β` is the eigenvariable such that `φ(r,β)`.
 * We store this as the production `β → r`.
 * Additionally, we require that there is *exactly one* production for each `β`
 * (this condition is missing from pre-grammars)
 */
case class Pi2PreGrammar(
    startSymbol: Var,
    alpha:       Var, betas: Vector[Var],
    productions: Vector[( Var, Expr )] ) {
  val nonTerminals = startSymbol +: betas :+ alpha
  require( nonTerminals == nonTerminals.distinct )

  for ( ( lhs, rhs ) <- productions; fvs = freeVariables( rhs ) ) {
    if ( lhs == startSymbol ) {
      require( fvs.subsetOf( Set( alpha ) ) || fvs.subsetOf( betas.toSet ) )
    } else if ( lhs == alpha ) {
      require( fvs.subsetOf( Set( alpha ) ) )
    } else {
      require( betas.contains( lhs ) )
      val allowedFVs = betas.dropWhile( _ != lhs ).drop( 1 ).toSet
      require( freeVariables( rhs ).subsetOf( allowedFVs ) )
    }
  }

  def tratg = TRATG( startSymbol, startSymbol +: alpha +: betas,
    productions.filter( p => p._1 == startSymbol ) ++
      ( for ( ( lhs, rhs ) <- productions if betas.contains( lhs ) )
        yield alpha -> rhs ) ++
      ( for {
        ( `alpha`, alphaRhs ) <- productions
        ( beta, betaRhs ) <- productions
        if betas.contains( beta )
      } yield beta -> Substitution( alpha -> betaRhs )( alphaRhs ) ) )

  def language = tratg.language

  def size = productions.size

  override def toString =
    productions.map { case ( lhs, rhs ) => s"${lhs.toUntypedString} -> ${rhs.toUntypedString}" }.mkString( "\n" )
}

class Pi2Grammar( preGrammar: Pi2PreGrammar )
  extends Pi2PreGrammar( preGrammar.startSymbol, preGrammar.alpha, preGrammar.betas, preGrammar.productions ) {
  for ( beta <- preGrammar.betas )
    require( productions.count( _._1 == beta ) == 1 )
}
object Pi2Grammar {
  def apply( preGrammar: Pi2PreGrammar ) = new Pi2Grammar( preGrammar )
}

object stablePi2Grammar {
  def apply( startSymbol: Var, alpha: Var, betas: Vector[Var], language: Traversable[Expr] ): Pi2PreGrammar = {
    val betaTy = betas.head.ty
    val argStableTermsBetas = stableTerms( folSubTerms( language ).filter( _.ty == betaTy ), betas )

    Pi2PreGrammar( startSymbol, alpha, betas,
      Vector() ++
        ( for ( rhs <- stableTerms( language, Seq( alpha ) ) ++ stableTerms( language, betas ) )
          yield startSymbol -> rhs ) ++
        ( for ( rhs <- stableTerms( folSubTerms( language ).filter( _.ty == alpha.ty ), Seq( alpha ) ) )
          yield alpha -> rhs ) ++
        ( for {
          ( beta, j ) <- betas.zipWithIndex
          allowedFVs = betas.drop( j + 1 ).toSet
          rhs <- argStableTermsBetas
          if freeVariables( rhs ).subsetOf( allowedFVs )
        } yield beta -> rhs ) )
  }
}

object minimizePi2Grammar {
  val logger = Logger( "minimizePi2Grammar" )

  def apply( g: Pi2PreGrammar, lang: Traversable[Expr], solver: MaxSATSolver ): Option[Pi2Grammar] = {
    def prodinc( p: ( Var, Expr ) ): Atom = Atom( "prodinc2", p._1, p._2 )

    val productionSources: Vector[( VTRATG.Production, List[( Var, Expr )] )] =
      ( for ( p @ ( lhs, rhs ) <- g.productions if lhs == g.startSymbol )
        yield ( List( lhs ) -> List( rhs ) ) -> List( p ) ) ++
        ( for ( p @ ( lhs, rhs ) <- g.productions if g.betas contains lhs )
          yield ( List( g.alpha ) -> List( rhs ) ) -> List( p ) ) ++
        ( for {
          p1 @ ( g.alpha, alphaRhs ) <- g.productions
          p2 @ ( beta, betaRhs ) <- g.productions
          if g.betas.contains( beta )
        } yield ( List( beta ) -> List( Substitution( g.alpha -> betaRhs )( alphaRhs ) ) ) -> List( p1, p2 ) )

    val tratg = VTRATG( g.startSymbol, List( g.startSymbol ) +: List( g.alpha ) +: g.betas.map( List( _ ) ),
      productionSources.map( _._1 ).toSet )
    val tratgFormula = new VectGrammarMinimizationFormula( tratg )

    val correspondenceFormula =
      And( for ( ( vtratgP, pi2Ps ) <- productionSources.groupBy( _._1 ) )
        yield tratgFormula.productionIsIncluded( vtratgP ) --> Or( pi2Ps.map( ps => And( ps._2.map( prodinc ) ) ) ) )

    val betaCardinality =
      And( for ( beta <- g.betas ) yield thresholds.exactly.oneOf(
        for ( p <- g.productions if p._1 == beta ) yield prodinc( p ) ) )

    // FIXME: heuristic 1) is broken if the quantified variables do not occur in all atoms
    // e.g.: ⊢ ∃x ∃y ∃z ∃w (P x y ∧ P y z ∧ P z w)
    // Here the production τ → r₂(x, β₃, β₂, β₁) is completely acceptable.

    // Heuristic 1)
    // Whenever we have a production τ → t[β₃, ‥] then we require that it is actually of the
    // form τ → t[β₃, r₃], where t does not contain any β and β₃ → r₃
    val expressibilityCondition = And( for {
      ( lhs, rhs ) <- g.productions
      if lhs == g.startSymbol
      fvs = freeVariables( rhs )
      if fvs.size > 1
      if fvs.intersect( g.betas.toSet ).nonEmpty
    } yield prodinc( lhs -> rhs ) --> Or {
      for {
        ( lhs2, rhs2 ) <- g.productions
        if g.betas.contains( lhs2 )
        rhs_ = TermReplacement( rhs, rhs2, lhs2 )
        if freeVariables( rhs_ ) == Set( lhs2 )
      } yield prodinc( lhs2 -> rhs2 )
    } )

    // Heuristic 2)
    // We require that the set of α-productions is nonempty.
    val alphaNonempty = Or( for ( p @ ( lhs, _ ) <- g.productions if lhs == g.alpha ) yield prodinc( p ) )

    val hard = tratgFormula.coversLanguage( lang ) & correspondenceFormula & betaCardinality &
      expressibilityCondition & alphaNonempty
    logger.metric( "minform_lcomp", lcomp( simplify( toNNF( hard ) ) ) )

    val soft = for ( p <- g.productions ) yield -prodinc( p ) -> 1

    solver.solve( hard, soft ).map { assg =>
      Pi2Grammar( g.copy( productions = g.productions.filter( p => assg( prodinc( p ) ) ) ) )
    }
  }
}

object findMinimalPi2Grammar {
  val logger = minimizePi2Grammar.logger

  def apply( lang: Traversable[Expr], alpha: Var, betas: Vector[Var], solver: MaxSATSolver ): Option[Pi2Grammar] = {
    require( freeVariables( lang ).isEmpty )
    val startSymbol = rename( Var( "x0", lang.head.ty ), alpha +: betas )
    val stableG = logger.time( "stabgrammar" ) { stablePi2Grammar( startSymbol, alpha, betas, lang ) }
    logger.metric( "stabgrammar", stableG.size )
    logger.time( "mingrammar" ) { minimizePi2Grammar( stableG, lang, solver ) }
  }
}
