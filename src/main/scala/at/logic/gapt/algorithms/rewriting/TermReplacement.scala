
package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.utils.logging.Logger
import at.logic.gapt.proofs.{ HOLSequent, resolution }

import scala.collection.mutable

/**
 * ***** Term Replacement **********
 * replaces all occurences of term "what" by term "by" in term "term" -- be careful with replacing variables,
 * there is no scope checking
 *
 * usable on subclasses of lambda expressions and fsequents
 */
object TermReplacement extends Logger {
  //TODO: this should go into the language layer (blocked because of the dependency on name replacement)

  def apply( term: LambdaExpression, what: LambdaExpression, by: LambdaExpression ): LambdaExpression = {
    require( what.exptype == by.exptype )
    rename_term( term, what, by )
  }

  def apply( f: HOLFormula, what: LambdaExpression, by: LambdaExpression ): HOLFormula = {
    require( what.exptype == by.exptype )
    rename_term( f.asInstanceOf[LambdaExpression], what, by ).asInstanceOf[HOLFormula]
  }

  def apply( term: HOLFormula, p: Map[LambdaExpression, LambdaExpression] ): HOLFormula =
    apply( term.asInstanceOf[LambdaExpression], p ).asInstanceOf[HOLFormula]

  def apply( term: LambdaExpression, p: Map[LambdaExpression, LambdaExpression] ): LambdaExpression =
    p.foldLeft( term )( ( t, x ) => {
      /*debug(1,"looking for "+x+" in "+t);*/ apply( t, x._1, x._2 )
    } )

  def apply( term: FOLExpression, p: Map[FOLExpression, FOLExpression] ): FOLExpression =
    p.foldLeft( term )( ( t, x ) => {
      /*debug(1,"looking for "+x+" in "+t);*/ apply( t, x._1, x._2 ).asInstanceOf[FOLExpression]
    } )

  def apply( t: FOLTerm, map: Map[FOLTerm, FOLTerm] ): FOLTerm =
    apply( t.asInstanceOf[FOLExpression], map.asInstanceOf[Map[FOLExpression, FOLExpression]] ).asInstanceOf[FOLTerm]

  def apply( f: FOLFormula, map: Map[FOLTerm, FOLTerm] ): FOLFormula =
    apply( f.asInstanceOf[FOLExpression], map.asInstanceOf[Map[FOLExpression, FOLExpression]] ).asInstanceOf[FOLFormula]

  def apply( f: FOLAtom, map: Map[FOLTerm, FOLTerm] ): FOLAtom =
    apply( f.asInstanceOf[FOLExpression], map.asInstanceOf[Map[FOLExpression, FOLExpression]] ).asInstanceOf[FOLAtom]

  // FIXME: these polymorphic functions do not have the types you think they have...

  def rename_fsequent( fs: HOLSequent, what: LambdaExpression, by: LambdaExpression ): HOLSequent =
    HOLSequent(
      fs.antecedent.map( apply( what, by, _ ).asInstanceOf[HOLFormula] ),
      fs.succedent.map( apply( what, by, _ ).asInstanceOf[HOLFormula] )
    )

  def rename_fsequent( fs: HOLSequent, p: Map[LambdaExpression, LambdaExpression] ): HOLSequent = {
    HOLSequent(
      fs.antecedent.map( apply( _, p ) ),
      fs.succedent.map( apply( _, p ) )
    )
  }

  def rename_term( term: LambdaExpression, what: LambdaExpression, by: LambdaExpression ): LambdaExpression = {
    if ( term == what ) by
    else
      term match {
        case Var( s, t ) =>
          if ( what == term ) by else term
        case Const( s, t ) =>
          if ( what == term ) by else term
        case App( s, t ) =>
          val s_ = rename_term( s, what, by )
          val t_ = rename_term( t, what, by )
          App( s_, t_ )
        case Abs( x, t ) =>
          val t_ = rename_term( t, what, by )
          Abs( x, t_ )
      }
  }

  def apply( proof: resolution.ResolutionProof, repl: Map[FOLTerm, FOLTerm] ): resolution.ResolutionProof = {
    import resolution._
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()

    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case InputClause( clause )     => InputClause( clause map { TermReplacement( _, repl ) } )
      case ReflexivityClause( term ) => ReflexivityClause( TermReplacement( term, repl ) )
      case TautologyClause( atom )   => TautologyClause( TermReplacement( atom, repl ) )
      case Factor( q, i1, i2 )       => Factor( f( q ), i1, i2 )
      case Instance( q, subst ) =>
        Instance( f( q ), FOLSubstitution( subst.folmap.map { case ( f, t ) => f -> TermReplacement( t, repl ) } ) )
      case Resolution( q1, l1, q2, l2 ) => Resolution( f( q1 ), l1, f( q2 ), l2 )
      case Paramodulation( q1, l1, q2, l2, pos, dir ) =>
        Paramodulation( f( q1 ), l1, f( q2 ), l2, pos, dir )
    } )

    f( proof )
  }
}

