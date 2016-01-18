
package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion.{ replaceET, ExpansionTree }
import at.logic.gapt.proofs.{ HOLSequent, resolution, lk }

import scala.collection.mutable

/**
 * ***** Term Replacement **********
 * replaces all occurences of term "what" by term "by" in term "term" -- be careful with replacing variables,
 * there is no scope checking
 *
 * usable on subclasses of lambda expressions and fsequents
 */
object TermReplacement {
  //TODO: this should go into the language layer (blocked because of the dependency on name replacement)

  def apply( term: LambdaExpression, what: LambdaExpression, by: LambdaExpression ): LambdaExpression =
    apply( term, Map( what -> by ) )

  def apply( f: HOLFormula, what: LambdaExpression, by: LambdaExpression ): HOLFormula =
    apply( f, Map( what -> by ) )

  def apply( term: HOLFormula, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLFormula =
    apply( term.asInstanceOf[LambdaExpression], p ).asInstanceOf[HOLFormula]

  def apply( term: HOLAtom, p: PartialFunction[LambdaExpression, LambdaExpression] ): HOLAtom =
    apply( term.asInstanceOf[LambdaExpression], p ).asInstanceOf[HOLAtom]

  def apply( term: LambdaExpression, map: PartialFunction[LambdaExpression, LambdaExpression] ): LambdaExpression =
    term match {
      case _ if map isDefinedAt term => map( term )

      // special case polymorphic constants so that we can do type-changing replacements
      // but only if the user doesn't specify any replacement for the logical constants
      case Eq( s, t ) if !( map isDefinedAt EqC( s.exptype ) ) =>
        Eq( apply( s, map ), apply( t, map ) )
      case All( x, t ) if !( map isDefinedAt ForallC( x.exptype ) ) =>
        All( apply( x, map ).asInstanceOf[Var], apply( t, map ) )
      case Ex( x, t ) if !( map isDefinedAt ExistsC( x.exptype ) ) =>
        Ex( apply( x, map ).asInstanceOf[Var], apply( t, map ) )

      case App( s, t ) =>
        App( apply( s, map ), apply( t, map ) )
      case Abs( x, t ) =>
        Abs( apply( x, map ).asInstanceOf[Var], apply( t, map ) )

      case _ => term
    }

  def apply( term: FOLExpression, map: PartialFunction[FOLExpression, FOLExpression] ): FOLExpression =
    apply( term.asInstanceOf[LambdaExpression], map.asInstanceOf[PartialFunction[LambdaExpression, LambdaExpression]] ).asInstanceOf[FOLExpression]

  def apply( t: FOLTerm, map: PartialFunction[FOLTerm, FOLTerm] ): FOLTerm =
    apply( t.asInstanceOf[FOLExpression], map.asInstanceOf[PartialFunction[FOLExpression, FOLExpression]] ).asInstanceOf[FOLTerm]

  def apply( f: FOLFormula, map: PartialFunction[FOLTerm, FOLTerm] ): FOLFormula =
    apply( f.asInstanceOf[FOLExpression], map.asInstanceOf[PartialFunction[FOLExpression, FOLExpression]] ).asInstanceOf[FOLFormula]

  def apply( f: FOLAtom, map: PartialFunction[FOLTerm, FOLTerm] ): FOLAtom =
    apply( f.asInstanceOf[FOLExpression], map.asInstanceOf[PartialFunction[FOLExpression, FOLExpression]] ).asInstanceOf[FOLAtom]

  def apply( proof: resolution.ResolutionProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): resolution.ResolutionProof = {
    import resolution._
    val memo = mutable.Map[ResolutionProof, ResolutionProof]()

    def f( p: ResolutionProof ): ResolutionProof = memo.getOrElseUpdate( p, p match {
      case InputClause( clause )     => InputClause( clause map { TermReplacement( _, repl ) } )
      case ReflexivityClause( term ) => ReflexivityClause( TermReplacement( term, repl ) )
      case TautologyClause( atom )   => TautologyClause( TermReplacement( atom, repl ) )
      case Factor( q, i1, i2 )       => Factor( f( q ), i1, i2 )
      case Instance( q, subst ) =>
        Instance( f( q ), Substitution( subst.map.map { case ( f, t ) => f -> TermReplacement( t, repl ) } ) )
      case Resolution( q1, l1, q2, l2 ) => Resolution( f( q1 ), l1, f( q2 ), l2 )
      case Paramodulation( q1, l1, q2, l2, pos, dir ) =>
        Paramodulation( f( q1 ), l1, f( q2 ), l2, pos, dir )
    } )

    f( proof )
  }

  def apply( proof: lk.LKProof, repl: PartialFunction[LambdaExpression, LambdaExpression] ): lk.LKProof = {
    import lk._

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

      case InductionRule( cases, main ) =>
        InductionRule( cases map { c =>
          c.copy( apply( c.proof, repl ), constructor = apply( c.constructor, repl ).asInstanceOf[Const] )
        }, apply( main, repl ) )

      case DefinitionLeftRule( subProof, aux, main )  => DefinitionLeftRule( f( subProof ), aux, apply( main, repl ) )
      case DefinitionRightRule( subProof, aux, main ) => DefinitionRightRule( f( subProof ), aux, apply( main, repl ) )
    }

    f( proof )
  }

  def apply( expTree: ExpansionTree, map: PartialFunction[LambdaExpression, LambdaExpression] ): ExpansionTree =
    replaceET( expTree, map )
}

