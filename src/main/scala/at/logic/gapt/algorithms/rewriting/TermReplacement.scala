
package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.utils.logging.Logger
import NameReplacement.find_matching

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
}

/**
 * ***** Term Replacement **********
 * replaces all occurences of term "what" by term "by" in term "term" -- be careful with replacing variables,
 * there is no scope checking
 *
 * usable on resolution proofs
 */
object RenameResproof extends Logger {
  import TermReplacement._

  // map from sumbol name to pair of Arity and replacement symbol name
  type SymbolMap = Map[FOLTerm, FOLTerm]
  type OccMap = Map[FormulaOccurrence, FormulaOccurrence]
  type ProofMap = Map[RobinsonResolutionProof, ( OccMap, RobinsonResolutionProof )]

  val emptySymbolMap = Map[FOLTerm, FOLTerm]()
  val emptyOccMap = Map[FormulaOccurrence, FormulaOccurrence]()
  val emptyProofMap = Map[RobinsonResolutionProof, ( OccMap, RobinsonResolutionProof )]()

  def extendw_pmap( index: RobinsonResolutionProof, p: ProofMap, o: OccMap, i: RobinsonResolutionProof ) = ( p + ( ( index, ( o, i ) ) ), o, i )
  def add_pmap( pmap: ProofMap, parent: RobinsonResolutionProof ): ( ProofMap, OccMap, RobinsonResolutionProof ) = { val x = pmap( parent ); ( pmap, x._1, x._2 ) }

  def rename_resproof(
    p:      RobinsonResolutionProof,
    irules: Set[RobinsonResolutionProof],
    smap:   SymbolMap
  ): RobinsonResolutionProof = {
    //don't process the prove if there is nothing to do
    if ( smap.isEmpty ) p else rename_resproof( p, irules, smap, emptyProofMap )._1( p )._2
  }

  def rename_resproof(
    p:      RobinsonResolutionProof,
    irules: Set[RobinsonResolutionProof],
    smap:   SymbolMap,
    pmap:   ProofMap
  ): ( ProofMap, OccMap, RobinsonResolutionProof ) = {
    if ( pmap contains p ) add_pmap( pmap, p ) else
      p match {
        case InitialClause( clause ) =>
          val HOLSequent( fnegp, fposp ) = rename_fsequent( clause.toHOLSequent, smap.asInstanceOf[Map[LambdaExpression, LambdaExpression]] )
          val negp = fnegp.toList.asInstanceOf[List[FOLFormula]]
          val posp = fposp.toList.asInstanceOf[List[FOLFormula]]

          val inference = InitialClause( negp, posp )
          //create map form original iteral occs to renamed literal occs
          val negm: Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ ( clause.negative zip negp )
          val posm: Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ ( clause.positive zip posp )
          def nmatcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = negm( o ) == t.formula
          def pmatcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = posm( o ) == t.formula

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, nmatcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, pmatcher )

          extendw_pmap( p, pmap, rsmap, inference )

        case Variant( clause, parent1, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, irules, smap, pmap )
          val nsmap: Map[FOLVar, FOLTerm] = sub.folmap map ( x => ( x._1, apply( x._2, smap ) ) )
          val nsub = FOLSubstitution( nsmap )
          val inference: RobinsonResolutionProof = Variant( rparent1, nsub )

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == apply( o.formula.asInstanceOf[FOLFormula], smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Factor( clause, parent1, aux, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, irules, smap, pmap )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, apply( x._2, smap ) ) ) )
          val inference: RobinsonResolutionProof = aux match {
            case lit1 :: Nil =>
              Factor( rparent1, rmap( lit1.head ), lit1.tail map rmap, nsub )
            case lit1 :: lit2 :: Nil =>
              Factor( rparent1, rmap( lit1.head ), lit1.tail map rmap, rmap( lit2.head ), lit2.tail map rmap, nsub )
            case _ => throw new Exception( "Factor rule for " + p.root + " does not have one or two primary formulas! aux=" + aux )
          }

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == apply( o.formula.asInstanceOf[FOLFormula], smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Instance( clause, parent1, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, irules, smap, pmap )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, apply( x._2, smap ) ) ) )
          val inference: RobinsonResolutionProof = Instance( rparent1, nsub )
          trace( "sub=" + sub )
          trace( "nsub=" + nsub )
          trace( "inference: " + clause )
          trace( "ninference: " + inference.root )
          trace( "parent:    " + parent1.root )
          trace( "rparent:    " + rparent1.root )

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            trace( "anc corr in matcher:" )
            trace( anc_correspondences.toString )
            t.formula == apply( o.formula.asInstanceOf[FOLFormula], smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Resolution( clause, parent1, parent2, lit1, lit2, sub ) =>
          val ( rpmap1, rmap1, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, irules, smap, pmap )
          val ( rpmap2, rmap2, rparent2 ) = if ( pmap contains parent2 ) add_pmap( pmap, parent2 ) else rename_resproof( parent2, irules, smap, rpmap1 )
          val nsub = FOLSubstitution( sub.folmap map ( x => {
            val repl = apply( x._2, smap )
            ( x._1, repl )
          } ) )

          val inference = Resolution( rparent1, rparent2, rmap1( lit1 ), rmap2( lit2 ), nsub )
          val rmap = rmap1 ++ rmap2

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == apply( o.formula.asInstanceOf[FOLFormula], smap ).asInstanceOf[FOLFormula] &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap2, rsmap, inference )

        case Paramodulation( clause, parent1, parent2, lit1, lit2, _, sub ) =>
          val ( rpmap1, rmap1, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, irules, smap, pmap )
          val ( rpmap2, rmap2, rparent2 ) = if ( pmap contains parent2 ) add_pmap( pmap, parent2 ) else rename_resproof( parent2, irules, smap, rpmap1 )

          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, apply( x._2, smap ) ) ) )

          val Some( prim ) = clause.literals.map( _._1 ).find( occ => occ.parents == List( lit1, lit2 ) || occ.parents == List( lit2, lit1 ) )
          val nformula = apply( prim.formula.asInstanceOf[FOLFormula], smap ).asInstanceOf[FOLFormula]

          // this is the rule containing the introduction
          if ( irules contains parent1 ) {
            //TODO: add code for removing unneccesary parents: rewriting l to r, if the intrudoction rule was l=r before, it s now r=r and we can drop it
            //println("axiom rule 1 after replacement: "+rparent1)
          }
          if ( irules contains parent2 ) {
            //TODO: add code for removing unneccesary parents: rewriting l to r, if the intrudoction rule was l=r before, it s now r=r and we can drop it
            //println("axiom rule 2 after replacement: "+rparent2)
          }

          val inference = Paramodulation( rparent1, rparent2, rmap1( lit1 ), rmap2( lit2 ), nformula, nsub )
          val rmap = rmap1 ++ rmap2

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            //println("anc matcher")
            //println(o); println(o.ancestors)
            //println(t); println(t.ancestors)
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            //println(anc_correspondences)
            t.formula == apply( o.formula.asInstanceOf[FOLFormula], smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap2, rsmap, inference )

      }
  }
}

