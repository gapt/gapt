package at.logic.gapt.grammars.induction2

import at.logic.gapt.expr._
import InductionGrammar._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.grammars.VTRATG
import at.logic.gapt.proofs.{ Checkable, Context }

import scala.collection.mutable

case class InductionGrammar(
    tau:         Var,
    alpha:       Var,
    nu:          Map[Const, NonTerminalVect],
    gamma:       NonTerminalVect,
    productions: Vector[Production] ) {

  for ( Production( lhs, rhs ) <- productions ) {
    require( lhs == List( tau ) || lhs == gamma )
    val fvs = freeVariables( rhs )
    require( nu.values.exists( n => fvs.subsetOf( Set( alpha ) ++ gamma ++ n ) ) )
  }

  def nonTerminals: Vector[NonTerminalVect] =
    Vector( List( tau ), List( alpha ), gamma ) ++ nu.values

  def indTy: Ty =
    alpha.ty

  def subTerms( term: Expr ): Map[Const, Set[Expr]] = {
    val result = mutable.Map[Const, Set[Expr]]().withDefaultValue( Set() )
    def go( term: Expr ): Unit =
      term match {
        case Apps( c: Const, as ) =>
          result( c ) += term
          for ( a <- as if a.ty == term.ty ) go( a )
      }
    go( term )
    result.toMap
  }

  def determineNu( prod: Production ): Option[Const] = {
    val fvs = freeVariables( prod.rhs )
    if ( fvs.subsetOf( Set( alpha ) ++ gamma ) ) None else
      nu.find( n => fvs.subsetOf( Set( alpha ) ++ gamma ++ n._2 ) ).map( _._1 )
  }

  def instantiateProduction( prod: Production, t: Expr, subterms: Map[Const, Set[Expr]], gammas: Map[Expr, VTRATG.NonTerminalVect] ): Set[VTRATG.Production] = {
    val relevantSubterms = determineNu( prod ) match {
      case Some( n ) => subterms( n )
      case None      => subterms.values.flatten.toSet
    }
    val containsOnlyAlpha = freeVariables( prod.rhs ).subsetOf( Set( alpha ) )
    relevantSubterms.flatMap {
      case st @ Apps( c: Const, s ) =>
        val n = nu( c )
        val rhs = Substitution( ( alpha -> t ) +: ( n zip s ) ++: ( gamma zip gammas( st ) ) )( prod.rhs ).toList
        prod.lhs match {
          case List( `tau` ) => List( List( tau ) -> rhs )
          case g if !containsOnlyAlpha =>
            for ( si <- s if si.ty == t.ty ) yield gammas( si ) -> rhs
          case g if containsOnlyAlpha => List( gammas( st ) -> rhs )
        }
    }
  }

  def generateInstGammas( subterms: Map[Const, Set[Expr]] ): Vector[( Expr, VTRATG.NonTerminalVect )] = {
    val nameGen = rename.awayFrom( List( tau, alpha ) ++ gamma ++ nu.values.flatten )
    subterms.values.flatten.toVector.sortBy( folTermSize( _ ) ).map( s => s -> gamma.map( nameGen.fresh( _ ) ) )
  }

  def instantiate( t: Expr ): VTRATG = {
    val subterms = subTerms( t )
    val gammas = generateInstGammas( subterms )
    VTRATG( tau, Seq( List( tau ) ) ++ gammas.map( _._2 ),
      productions.view.flatMap( instantiateProduction( _, t, subterms, gammas.toMap ) ).toSet )
  }

}

object InductionGrammar {
  type NonTerminalVect = List[Var]

  case class Production( lhs: NonTerminalVect, rhs: List[Expr] ) {
    require( lhs.size == rhs.size )
  }

  object Production {
    def apply( lhs: Var, rhs: Expr ): Production = Production( List( lhs ), List( rhs ) )
  }

  implicit object checkable extends Checkable[InductionGrammar] {
    override def check( g: InductionGrammar )( implicit ctx: Context ): Unit = {
      for ( nt <- g.nonTerminals; x <- nt ) ctx.check( x )
      val Some( ctrs ) = ctx.getConstructors( g.indTy )
      require( g.nu.keySet == ctrs.toSet )
      for ( ctr @ Const( _, FunctionType( _, argTypes ) ) <- ctrs ) {
        val nu = g.nu( ctr )
        require( nu.size == argTypes.size )
        for ( ( nui, argType ) <- nu zip argTypes )
          require( nui.ty == argType )
      }
    }
  }
}
