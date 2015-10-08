
package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.utils.logging.Logger
import at.logic.gapt.proofs.{ HOLSequent, resolution, lkNew }

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

  def apply( term: HOLAtom, p: Map[LambdaExpression, LambdaExpression] ): HOLAtom =
    apply( term.asInstanceOf[LambdaExpression], p ).asInstanceOf[HOLAtom]

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

  def apply( proof: lkNew.LKProof, repl: Map[LambdaExpression, LambdaExpression] ): lkNew.LKProof = {
    import lkNew._

    def f( p: LKProof ): LKProof = p match {
      case TopAxiom => TopAxiom
      case BottomAxiom => BottomAxiom
      case ReflexivityAxiom( term ) => ReflexivityAxiom( apply( term, repl ) )
      case LogicalAxiom( atom ) => LogicalAxiom( apply( atom, repl ) )
      case TheoryAxiom( clause ) => TheoryAxiom( clause map { apply( _, repl ) } )

      case WeakeningLeftRule( subProof, formula ) => WeakeningLeftRule( f( subProof ), apply( formula, repl ) )
      case WeakeningRightRule( subProof, formula ) => WeakeningRightRule( f( subProof ), apply( formula, repl ) )

      case ContractionLeftRule( subProof, aux1, aux2 ) => ContractionLeftRule( f( subProof ), aux1, aux2 )
      case ContractionRightRule( subProof, aux1, aux2 ) => ContractionRightRule( f( subProof ), aux1, aux2 )

      case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) => CutRule( f( leftSubProof ), aux1, f( rightSubProof ), aux2 )

      case NegLeftRule( subProof, aux ) => NegLeftRule( f( subProof ), aux )
      case NegRightRule( subProof, aux ) => NegRightRule( f( subProof ), aux )

      case AndLeftRule( subProof, aux1, aux2 ) => AndLeftRule( f( subProof ), aux1, aux2 )
      case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) => AndRightRule( f( leftSubProof ), aux1, f( rightSubProof ), aux2 )

      case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) => OrLeftRule( f( leftSubProof ), aux1, f( rightSubProof ), aux2 )
      case OrRightRule( subProof, aux1, aux2 ) => OrRightRule( f( subProof ), aux1, aux2 )

      case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) => ImpLeftRule( f( leftSubProof ), aux1, f( rightSubProof ), aux2 )
      case ImpRightRule( subProof, aux1, aux2 ) => ImpRightRule( f( subProof ), aux1, aux2 )

      case ForallLeftRule( subProof, aux, formula, term, v ) => ForallLeftRule( f( subProof ), aux, apply( formula, repl ), apply( term, repl ), v )
      case ForallRightRule( subProof, aux, eigen, quant ) => ForallRightRule( f( subProof ), aux, eigen, quant )

      case ExistsLeftRule( subProof, aux, eigen, quant ) => ExistsLeftRule( f( subProof ), aux, eigen, quant )
      case ExistsRightRule( subProof, aux, formula, term, v ) => ExistsRightRule( f( subProof ), aux, apply( formula, repl ), apply( term, repl ), v )

      case EqualityLeftRule( subProof, eq, aux, pos ) => EqualityLeftRule( f( subProof ), eq, aux, pos )
      case EqualityRightRule( subProof, eq, aux, pos ) => EqualityRightRule( f( subProof ), eq, aux, pos )

      case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
        InductionRule( f( leftSubProof ), aux1, f( rightSubProof ), aux2, aux3, apply( term, repl ).asInstanceOf[FOLTerm] )

      case DefinitionLeftRule( subProof, aux, main )  => DefinitionLeftRule( f( subProof ), aux, apply( main, repl ) )
      case DefinitionRightRule( subProof, aux, main ) => DefinitionRightRule( f( subProof ), aux, apply( main, repl ) )
    }

    f( proof )
  }
}

