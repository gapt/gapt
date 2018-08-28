package gapt.grammars

import gapt.expr._
import gapt.expr.fol.{ folSubTerms, folTermSize }
import gapt.expr.hol.atoms
import gapt.formats.babel.{ BabelExporter, MapBabelSignature, Precedence }
import gapt.grammars.InductionGrammar._
import gapt.proofs.{ Checkable }
import gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import gapt.utils.{ Doc, NameGenerator }
import cats.instances.list._
import cats.syntax.traverse._
import gapt.proofs.context.Context

case class InductionGrammar(
    tau:         Var,
    alpha:       Var,
    nus:         Map[Const, NonTerminalVect],
    gamma:       List[Var],
    productions: Vector[Production] ) {

  for ( prod @ Production( lhs, rhs ) <- productions ) {
    require( lhs == List( tau ) || lhs == gamma, s"$lhs is not a nonterminal" )
    val fvs = freeVariables( rhs )
    require(
      nus.values.exists( n => fvs.subsetOf( Set( alpha ) ++ gamma ++ n ) ),
      s"production violates variable condition: $prod" )
  }

  def nonTerminals: Vector[NonTerminalVect] =
    Vector( List( tau ), List( alpha ), gamma ) ++ nus.values

  def terminals: Set[Const] =
    nus.keySet ++ constants( productions.flatMap( _.rhs ) )

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

  def instanceLanguage( term: Expr ): Set[Expr] = {
    val fvs = freeVariables( term )
    if ( fvs.isEmpty ) inst( term ).instanceGrammar.language else {
      val nameGen = rename.awayFrom( InductionGrammar.isReplaceable.names( this ) ++ containedNames( term ) )
      val grounding = for ( fv <- fvs ) yield fv -> nameGen.fresh( Const( fv.name, fv.ty ) )
      TermReplacement( instanceLanguage( Substitution( grounding )( term ) ), grounding.map( _.swap ).toMap )
    }
  }

  def filterProductions( pred: Production => Boolean ): InductionGrammar =
    copy( productions = productions.filter( pred ) )

  def gammaProductions: Vector[Production] =
    productions.filter( _.lhs == gamma )

  override def toString: String =
    new IndGExporter( unicode = true, this ).export

}

object InductionGrammar {
  type NonTerminalVect = List[Var]

  case class Production( lhs: NonTerminalVect, rhs: List[Expr] ) {
    require( lhs.size == rhs.size, s"sides of production have nonequal size: $this" )
    for ( ( l, r ) <- lhs zip rhs ) require( l.ty == r.ty )

    def zipped: List[( Var, Expr )] = lhs zip rhs
  }

  object Production {
    def apply( lhs: Var, rhs: Expr ): Production = Production( List( lhs ), List( rhs ) )
  }

  implicit object productionReplaceable extends ClosedUnderReplacement[Production] {
    override def replace( prod: Production, p: PartialFunction[Expr, Expr] ): Production =
      Production( TermReplacement( prod.lhs, p ).map( _.asInstanceOf[Var] ), TermReplacement( prod.rhs, p ) )

    override def names( prod: Production ): Set[VarOrConst] =
      containedNames( prod.lhs ++ prod.rhs )
  }

  implicit object isReplaceable extends ClosedUnderReplacement[InductionGrammar] {
    override def replace( g: InductionGrammar, p: PartialFunction[Expr, Expr] ): InductionGrammar =
      InductionGrammar(
        tau = TermReplacement( g.tau, p ).asInstanceOf[Var],
        alpha = TermReplacement( g.alpha, p ).asInstanceOf[Var],
        nus = TermReplacement( g.nus, p ).map {
          case ( c, nu ) =>
            c.asInstanceOf[Const] -> nu.map( _.asInstanceOf[Var] )
        },
        gamma = TermReplacement( g.gamma, p ).map( _.asInstanceOf[Var] ),
        productions = TermReplacement( g.productions, p ) )

    override def names( g: InductionGrammar ): Set[VarOrConst] =
      containedNames( g.nonTerminals ) ++ containedNames( g.productions )
  }

  implicit object checkable extends Checkable[InductionGrammar] {
    override def check( g: InductionGrammar )( implicit ctx: Context ): Unit = {
      for ( nt <- g.nonTerminals; x <- nt ) ctx.check( x )
      val Some( ctrs ) = ctx.getConstructors( g.indTy )
      require( g.nus.keySet == ctrs.toSet )
      for ( ctr @ Const( _, FunctionType( _, argTypes ), _ ) <- ctrs ) {
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
          val rhs = Substitution( List( alpha -> term ) ++ ( nus( c ) zip ss ) ++
            ( gamma zip instGammas( st ) ) )( prod.rhs )
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

  def defaultNonTerminalNames(
    nameGen: NameGenerator,
    indTy:   Ty, tauTy: Ty,
    gamma: NonTerminalVect )( implicit ctx: Context ): InductionGrammar = {
    val tau = nameGen.fresh( Var( "τ", tauTy ) )
    val alpha = nameGen.fresh( Var( "α", indTy ) )
    val nus = Map() ++ ctx.getConstructors( indTy ).get.map {
      case ctr @ Const( _, FunctionType( _, argTypes ), _ ) =>
        ctr -> argTypes.map( argTy => nameGen.fresh( Var( "ν", argTy ) ) )
    }
    InductionGrammar( tau, alpha, nus, gamma, Vector() )
  }
}

private class IndGExporter( unicode: Boolean, g: InductionGrammar )
  extends BabelExporter( unicode, MapBabelSignature( g.terminals ) ) {
  import Doc._

  def csep( docs: List[Doc] ): Doc = wordwrap( docs, "," )

  def showNt( nt: Var ): Doc = show( nt, false, Set(), Map() )._1.inPrec( 0 )
  def showNt( nt: List[Var] ): Doc = csep( nt.map( showNt ) )

  def export: String = {
    val knownTypes = g.terminals.map { c => c.name -> c }.toMap ++ g.nonTerminals.flatten.map( nt => nt.name -> nt )

    val ntDecl =
      "Start symbol: " <> showNt( g.tau ) <> line <>
        "Parameter: " <> showNt( g.alpha ) <> line <>
        "Quantifiers: " <> showNt( g.gamma ) <> line <>
        "Constructors: " <> csep( g.nus.toList.map {
          case ( c, nu ) => show( c( nu ), true, Set(), knownTypes )._1.inPrec( 0 )
        } )

    val prods = stack( g.productions.toList
      sortBy { case Production( as, ts ) => ( g.nonTerminals.indexOf( as ), ts.toString ) }
      map { p =>
        group( csep( p.zipped.map {
          case ( a, t ) =>
            group( group( show( a, false, Set(), knownTypes )._1.inPrec( Precedence.impl ) </> "→" ) </> nest(
              show( t, true, Set(), knownTypes )._1.inPrec( Precedence.impl ) ) )
        } ) ) <> line
      } )

    group( ntDecl <> line <> line <> prods ).render( lineWidth )
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
  def apply( g: InductionGrammar, indexedTermset: Map[Expr, Set[Expr]],
             solver:    MaxSATSolver      = bestAvailableMaxSatSolver,
             weighting: Production => Int = _ => 1 ): Option[InductionGrammar] = {
    val formula = InductionGrammarMinimizationFormula( g )
    val hard = formula.coversIndexedTermset( indexedTermset )
    val soft = for ( p <- g.productions ) yield -formula.productionIsIncluded( p ) -> weighting( p )
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
    val defaultNames = InductionGrammar.defaultNonTerminalNames(
      nameGen, indexedTermset.keys.head.ty, indexedTermset.values.view.flatten.head.ty, gamma )
    apply( indexedTermset, defaultNames.tau, defaultNames.alpha, defaultNames.nus, gamma, solver )
  }
  def apply(
    indexedTermset: Map[Expr, Set[Expr]],
    tau:            Var, alpha: Var, nus: Map[Const, NonTerminalVect], gamma: NonTerminalVect,
    solver: MaxSATSolver ): Option[InductionGrammar] =
    apply( indexedTermset, tau, alpha, nus, gamma, solver, _ => 1 )

  def apply(
    indexedTermset: Map[Expr, Set[Expr]],
    tau:            Var, alpha: Var, nus: Map[Const, NonTerminalVect], gamma: NonTerminalVect,
    solver: MaxSATSolver, weighting: Production => Int ): Option[InductionGrammar] = {
    val stable = stableInductionGrammar( indexedTermset, tau, alpha, nus, gamma )
    minimizeInductionGrammar( stable, indexedTermset, solver, weighting )
  }
}
