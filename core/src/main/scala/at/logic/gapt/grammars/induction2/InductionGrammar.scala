package at.logic.gapt.grammars.induction2

import at.logic.gapt.expr._
import InductionGrammar._
import at.logic.gapt.expr.fol.{ folSubTerms, folTermSize }
import at.logic.gapt.grammars.VTRATG
import at.logic.gapt.proofs.{ Checkable, Context }

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
