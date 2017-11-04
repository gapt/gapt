package at.logic.gapt.grammars.induction2

import at.logic.gapt.expr._
import InductionGrammar._
import at.logic.gapt.expr.fol.{ folSubTerms, folTermSize }
import at.logic.gapt.expr.hol.atoms
import at.logic.gapt.grammars.{ VTRATG, VectGrammarMinimizationFormula, stableTerms }
import at.logic.gapt.proofs.{ Checkable, Context }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import cats.syntax.traverse._
import cats.instances.list._

case class InductionGrammar(
    tau:         Var,
    alpha:       Var,
    nus:         Map[Const, NonTerminalVect],
    gamma:       NonTerminalVect,
    productions: Vector[Production] ) {

  for ( Production( lhs, rhs ) <- productions ) {
    require( lhs == List( tau ) || lhs == gamma )
    val fvs = freeVariables( rhs )
    require( nus.values.exists( n => fvs.subsetOf( Set( alpha ) ++ gamma ++ n ) ) )
  }

  def nonTerminals: Vector[NonTerminalVect] =
    Vector( List( tau ), List( alpha ), gamma ) ++ nus.values

  def indTy: Ty =
    alpha.ty

  def size: Int =
    productions.size

  /**
   * Returns the constructor constant Some(cᵢ) if `prod` contains a
   * non-terminal νᵢⱼ, or None if `prod` contains no νᵢⱼ.
   */
  def correspondingCase( prod: Production ): Option[Const] = {
    val fvs = freeVariables( prod.rhs )
    if ( fvs.subsetOf( Set( alpha ) ++ gamma ) ) None else
      nus.find( n => fvs.subsetOf( Set( alpha ) ++ gamma ++ n._2 ) ).map( _._1 )
  }

  def defaultInstGammas( term: Expr ): Map[Expr, VTRATG.NonTerminalVect] = {
    val nameGen = rename.awayFrom( List( tau, alpha ) ++ gamma ++ nus.values.flatten )
    folSubTerms( term ).filter( _.ty == term.ty ).map( s => s -> gamma.map( nameGen.fresh( _ ) ) ).toMap
  }

  def inst( term: Expr ): Instantiation =
    Instantiation( this, term, defaultInstGammas( term ) )

  def instanceGrammar( term: Expr ): VTRATG =
    inst( term ).instanceGrammar

  def instanceLanguage( term: Expr ): Set[Expr] =
    inst( term ).instanceGrammar.language

  def filterProductions( pred: Production => Boolean ): InductionGrammar =
    copy( productions = productions.filter( pred ) )

}

object InductionGrammar {
  type NonTerminalVect = List[Var]

  case class Production( lhs: NonTerminalVect, rhs: List[Expr] ) {
    require( lhs.size == rhs.size )
    for ( ( l, r ) <- lhs zip rhs ) require( l.ty == r.ty )
  }

  object Production {
    def apply( lhs: Var, rhs: Expr ): Production = Production( List( lhs ), List( rhs ) )
  }

  implicit object checkable extends Checkable[InductionGrammar] {
    override def check( g: InductionGrammar )( implicit ctx: Context ): Unit = {
      for ( nt <- g.nonTerminals; x <- nt ) ctx.check( x )
      val Some( ctrs ) = ctx.getConstructors( g.indTy )
      require( g.nus.keySet == ctrs.toSet )
      for ( ctr @ Const( _, FunctionType( _, argTypes ) ) <- ctrs ) {
        val nu = g.nus( ctr )
        require( nu.size == argTypes.size )
        for ( ( nui, argType ) <- nu zip argTypes )
          require( nui.ty == argType )
      }
    }
  }

  case class Instantiation( grammar: InductionGrammar, term: Expr,
                            instGammas: Map[Expr, VTRATG.NonTerminalVect] ) {
    import grammar._

    val subterms: Set[Expr] = instGammas.keySet

    def instanceProductions( prod: Production ): Set[VTRATG.Production] = {
      val containsOnlyAlpha = freeVariables( prod.rhs ).subsetOf( Set( grammar.alpha ) )
      val prodCase = correspondingCase( prod )
      subterms.flatMap {
        case st @ Apps( c: Const, ss ) if prodCase.forall( _ == c ) =>
          val rhs = Substitution( List( alpha -> term ) ++ ( nus( c ) zip ss ) ++ ( gamma zip instGammas( st ) ) )( prod.rhs )
          prod.lhs match {
            case List( `tau` )          => List( List( tau ) -> rhs )
            case g if containsOnlyAlpha => List( instGammas( st ) -> rhs )
            case g if !containsOnlyAlpha =>
              for ( si <- ss if si.ty == term.ty ) yield instGammas( si ) -> rhs
          }
        case _ => Nil
      }
    }

    def instanceGrammar: VTRATG = {
      VTRATG( tau, Seq( List( tau ) ) ++ instGammas.toVector.sortBy( g => folTermSize( g._1 ) ).map( _._2 ),
        productions.view.flatMap( instanceProductions ).toSet )
    }
  }
}

object stableInductionGrammar {
  def apply( indexedTermset: Map[Expr, Set[Expr]], tau: Var, alpha: Var, nus: Map[Const, NonTerminalVect], gamma: NonTerminalVect ): InductionGrammar = {
    val terms = indexedTermset.values.flatten.toSet
    val tauProds = nus.toVector.flatMap {
      case ( _, nu ) =>
        val stable = stableTerms( terms, Seq( alpha ) ++ nu ++ gamma ).toList
        stable.map( Production( tau, _ ) )
    }.distinct
    val gammaProds = if ( gamma.isEmpty ) Vector() else {
      val subTerms = terms.flatMap { case Apps( _, as ) => folSubTerms( as ) }
      nus.toVector.flatMap {
        case ( _, nu ) =>
          val stable = stableTerms( subTerms, Seq( alpha ) ++ nu ++ gamma ).toList
          gamma.traverse[List, Expr]( g => stable.filter( _.ty == g.ty ) ).map( Production( gamma, _ ) )
      }.distinct
    }
    InductionGrammar( tau, alpha, nus, gamma, tauProds ++ gammaProds )
  }
}

case class InductionGrammarMinimizationFormula( g: InductionGrammar ) {
  def productionIsIncluded( p: Production ) = Atom( "prodinc", p.lhs ++ p.rhs )

  def coversIndexedTermset( openIndexedTermset: Map[Expr, Set[Expr]] ): Formula = {
    val grounding = Substitution {
      val nameGen = rename.awayFrom( containedNames( openIndexedTermset ) )
      freeVariables( openIndexedTermset.keys ).map { case v @ Var( n, t ) => v -> nameGen.fresh( Const( n, t ) ) }
    }
    val indexedTermset = openIndexedTermset.map( grounding( _ ) )
    val cs = Seq.newBuilder[Formula]
    for ( ( n, ts ) <- indexedTermset ) {
      val inst = g.inst( n )
      val vtratgMinForm = new VectGrammarMinimizationFormula( inst.instanceGrammar ) {
        override def productionIsIncluded( p: VTRATG.Production ) = Atom( "instprodinc", Seq( n ) ++ p._1 ++ p._2 )
        override def valueOfNonTerminal( t: Expr, a: Var, rest: Expr ) = Atom( "instntval", Seq( n, t, a, rest ) )
      }
      val instanceCovForm = vtratgMinForm.coversLanguage( ts )
      cs += instanceCovForm

      val atomsInInstForm = atoms( instanceCovForm )

      ( for ( p <- g.productions; instP <- inst.instanceProductions( p ) ) yield instP -> p ).
        groupBy( _._1 ).values.foreach { l =>
          val vtratgProdInc = vtratgMinForm.productionIsIncluded( l.head._1 )
          if ( atomsInInstForm contains vtratgProdInc )
            cs += vtratgProdInc --> Or( l.map( _._2 ).map( productionIsIncluded ) )
        }
    }
    And( cs.result )
  }
}

object minimizeInductionGrammar {
  def apply( g: InductionGrammar, indexedTermset: Map[Expr, Set[Expr]], solver: MaxSATSolver = bestAvailableMaxSatSolver ): Option[InductionGrammar] = {
    val formula = InductionGrammarMinimizationFormula( g )
    val hard = formula.coversIndexedTermset( indexedTermset )
    val soft = for ( p <- g.productions ) yield -formula.productionIsIncluded( p ) -> 1
    solver.solve( hard, soft ).map( model =>
      g.filterProductions( p => model( formula.productionIsIncluded( p ) ) ) )
  }
}

object findMinimalInductionGrammar {
  def apply( indexedTermset: Map[Expr, Set[Expr]], gamma: NonTerminalVect )( implicit ctx: Context ): Option[InductionGrammar] =
    apply( indexedTermset, gamma, bestAvailableMaxSatSolver )

  def apply(
    indexedTermset: Map[Expr, Set[Expr]],
    tau:            Var, alpha: Var, nus: Map[Const, NonTerminalVect], gamma: NonTerminalVect ): Option[InductionGrammar] =
    apply( indexedTermset, tau, alpha, nus, gamma, bestAvailableMaxSatSolver )

  def apply( indexedTermset: Map[Expr, Set[Expr]], gamma: NonTerminalVect,
             solver: MaxSATSolver )( implicit ctx: Context ): Option[InductionGrammar] = {
    val nameGen = rename.awayFrom( containedNames( indexedTermset ) ++ gamma )
    val tau = nameGen.fresh( Var( "τ", indexedTermset.values.view.flatten.head.ty ) )
    val indTy = indexedTermset.keys.head.ty
    val alpha = nameGen.fresh( Var( "α", indTy ) )
    val nus = Map() ++ ctx.getConstructors( indTy ).get.map {
      case ctr @ Const( _, FunctionType( _, argTypes ) ) =>
        ctr -> argTypes.map( argTy => nameGen.fresh( Var( "ν", argTy ) ) )
    }
    apply( indexedTermset, tau, alpha, nus, gamma, solver )
  }

  def apply(
    indexedTermset: Map[Expr, Set[Expr]],
    tau:            Var, alpha: Var, nus: Map[Const, NonTerminalVect], gamma: NonTerminalVect,
    solver: MaxSATSolver ): Option[InductionGrammar] = {
    val stable = stableInductionGrammar( indexedTermset, tau, alpha, nus, gamma )
    minimizeInductionGrammar( stable, indexedTermset, solver )
  }
}
