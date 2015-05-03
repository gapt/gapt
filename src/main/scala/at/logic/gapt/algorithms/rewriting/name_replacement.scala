package at.logic.gapt.algorithms.rewriting

import at.logic.gapt.expr.types._
import at.logic.gapt.expr._
import at.logic.gapt.language.fol.FOLSubstitution
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.proofs.resolution.Clause
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.expr.symbols.StringSymbol

/**
 * performs renaming of constants, functions and predicate symbols
 */
object NameReplacement {

  def apply( exp: LambdaExpression, map: SymbolMap ): LambdaExpression = renameSymbols( exp, map )
  def apply( exp: FOLExpression, map: SymbolMap ): FOLExpression = renameSymbols( exp, map )
  def apply( exp: Formula, map: SymbolMap ): Formula = renameSymbols( exp, map )
  def apply( exp: FOLFormula, map: SymbolMap ): FOLFormula = renameSymbols( exp, map )

  def apply( fs: FSequent, map: SymbolMap ) = renameFSequent( fs, map )
  def apply( p: RobinsonResolutionProof, map: SymbolMap ): RobinsonResolutionProof = {
    //don't process the proof if there is nothing to do
    if ( map.isEmpty ) p else rename_resproof( p, map )._2
  }

  // map from symbol name to pair of Arity and replacement symbol name
  type SymbolMap = Map[String, ( Int, String )]
  val emptySymbolMap = Map[String, ( Int, String )]()

  // The following code is duplicated because there is a class cast exception
  // in one of the tests if I have only the one for HOL. The problem is the 
  // reconstruction of constants. Create a method that changes only the names
  // in the objects without re-instantiating it??
  // It seems this is used only for FOL though...
  // TODO: think of a way to implement this and remove the duplication.

  def renameSymbols( exp: LambdaExpression, map: SymbolMap ): LambdaExpression = exp match {

    case Var( _, _ ) => exp

    case Const( name, exptype ) => map.get( name ) match {
      case Some( ( rarity, rname ) ) =>
        if ( Arity( exptype ) == rarity ) {
          Const( StringSymbol( rname ), exptype )
        } else {
          exp
        }
      case None => exp
    }

    case HOLAtom( x: Var, args )       => HOLAtom( x, args.map( a => renameSymbols( a, map ) ) )
    case HOLAtom( x: Const, args )     => HOLAtom( renameSymbols( x, map ).asInstanceOf[Const], args.map( a => renameSymbols( a, map ) ) )
    case HOLFunction( x: Var, args )   => HOLFunction( x, args.map( a => renameSymbols( a, map ) ) )
    case HOLFunction( x: Const, args ) => HOLFunction( renameSymbols( x, map ).asInstanceOf[Const], args.map( a => renameSymbols( a, map ) ) )
    case And( x, y )                   => And( renameSymbols( x, map ), renameSymbols( y, map ) )
    case Eq( x, y )                    => Eq( renameSymbols( x, map ), renameSymbols( y, map ) )
    case Or( x, y )                    => Or( renameSymbols( x, map ), renameSymbols( y, map ) )
    case Imp( x, y )                   => Imp( renameSymbols( x, map ), renameSymbols( y, map ) )
    case Neg( x )                      => Neg( renameSymbols( x, map ) )
    // Variables are not renamed
    case Ex( x, f )                    => Ex( x, renameSymbols( f, map ) )
    case All( x, f )                   => All( x, renameSymbols( f, map ) )
  }

  def renameSymbols( exp: FOLExpression, map: SymbolMap ): FOLExpression =
    renameSymbols( exp.asInstanceOf[LambdaExpression], map ).asInstanceOf[FOLExpression]

  def renameSymbols( exp: Formula, map: SymbolMap ): Formula =
    renameSymbols( exp.asInstanceOf[LambdaExpression], map ).asInstanceOf[Formula]

  def renameSymbols( exp: FOLFormula, map: SymbolMap ): FOLFormula =
    renameSymbols( exp.asInstanceOf[LambdaExpression], map ).asInstanceOf[FOLFormula]

  // Yes, this sucks. But it was the easiest and fastest way to deal with 
  // FSequents which are supposed to have FOLFormulas instead of Formulas.
  def rename_symbols_bla( f: Formula, map: SymbolMap ) = f.isInstanceOf[FOLFormula] match {
    case true  => renameSymbols( f.asInstanceOf[FOLFormula], map )
    case false => renameSymbols( f, map )
  }

  def renameFSequent( fs: FSequent, map: SymbolMap ) =
    FSequent( fs.antecedent map ( rename_symbols_bla( _, map ) ), fs.succedent map ( rename_symbols_bla( _, map ) ) )

  //def rename_substitution(sub : Substitution, map : SymbolMap) : Substitution = {
  //  Substitution(for ( (key,value) <- sub.map) yield { (key, apply(value, map)) } )
  //}

  type OccMap = Map[FormulaOccurrence, FormulaOccurrence]
  type ProofMap = Map[RobinsonResolutionProof, ( OccMap, RobinsonResolutionProof )]
  val emptyProofMap = Map[RobinsonResolutionProof, ( OccMap, RobinsonResolutionProof )]()

  def extendw_pmap( index: RobinsonResolutionProof, p: ProofMap, o: OccMap, i: RobinsonResolutionProof ) = ( p + ( ( index, ( o, i ) ) ), o, i )
  def add_pmap( pmap: ProofMap, parent: RobinsonResolutionProof ): ( ProofMap, OccMap, RobinsonResolutionProof ) = { val x = pmap( parent ); ( pmap, x._1, x._2 ) }

  def rename_resproof( p: RobinsonResolutionProof, smap: SymbolMap ): ( OccMap, RobinsonResolutionProof ) = rename_resproof( p, smap, emptyProofMap )._1( p )

  def rename_resproof( p: RobinsonResolutionProof, smap: SymbolMap, pmap: ProofMap ): ( ProofMap, OccMap, RobinsonResolutionProof ) = {
    if ( pmap contains p ) add_pmap( pmap, p ) else
      p match {
        case InitialClause( clause ) =>
          //rename literals
          val negp: List[FOLFormula] = clause.negative.toList map ( _.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) )
          val posp: List[FOLFormula] = clause.positive.toList map ( _.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) )
          val inference = InitialClause( negp, posp )
          //create map form original iteral occs to renamed literal occs
          val negm: Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ ( clause.negative zip negp )
          val posm: Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ ( clause.positive zip posp )
          def nmatcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = negm( o ) == t.formula
          def pmatcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = posm( o ) == t.formula

          //println(negm ++ posm)
          //println(clause)
          //println(inference.root)
          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, nmatcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, pmatcher )

          extendw_pmap( p, pmap, rsmap, inference )

        case Variant( clause, parent1, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, smap, pmap )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, x._2.renameSymbols( smap ) ) ) )
          var inference: RobinsonResolutionProof = Variant( rparent1, nsub )

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == o.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Factor( clause, parent1, aux, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, smap, pmap )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, x._2.renameSymbols( smap ) ) ) )
          var inference: RobinsonResolutionProof = aux match {
            case lit1 :: Nil =>
              Factor( rparent1, rmap( lit1.head ), lit1.tail map rmap, nsub )
            case lit1 :: lit2 :: Nil =>
              Factor( rparent1, rmap( lit1.head ), lit1.tail map rmap, rmap( lit2.head ), lit2.tail map rmap, nsub )
            case _ => throw new Exception( "Factor rule for " + p.root + " does not have one or two primary formulas! aux=" + aux )
          }

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == o.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Instance( clause, parent1, sub ) =>
          val ( rpmap, rmap, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, smap, pmap )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, x._2.renameSymbols( smap ) ) ) )
          var inference: RobinsonResolutionProof = Instance( rparent1, nsub )

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            t.formula == o.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap, rsmap, inference )

        case Resolution( clause, parent1, parent2, lit1, lit2, sub ) =>
          val ( rpmap1, rmap1, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, smap, pmap )
          val ( rpmap2, rmap2, rparent2 ) = if ( pmap contains parent2 ) add_pmap( pmap, parent2 ) else rename_resproof( parent2, smap, rpmap1 )
          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, x._2.renameSymbols( smap ) ) ) )
          val inference = Resolution( rparent1, rparent2, rmap1( lit1 ), rmap2( lit2 ), nsub )
          val rmap = rmap1 ++ rmap2

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            //println("anc matcher")
            //println(o); println(o.ancestors)
            //println(t); println(t.ancestors)
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            //println(anc_correspondences)
            t.formula == o.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap2, rsmap, inference )

        case Paramodulation( clause, parent1, parent2, lit1, lit2, _, sub ) =>
          val ( rpmap1, rmap1, rparent1 ) = if ( pmap contains parent1 ) add_pmap( pmap, parent1 ) else rename_resproof( parent1, smap, pmap )
          val ( rpmap2, rmap2, rparent2 ) = if ( pmap contains parent2 ) add_pmap( pmap, parent2 ) else rename_resproof( parent2, smap, rpmap1 )

          val nsub = FOLSubstitution( sub.folmap map ( x => ( x._1, x._2.renameSymbols( smap ) ) ) )

          val Some( prim ) = clause.literals.map( _._1 ).find( occ => occ.parents == List( lit1, lit2 ) || occ.parents == List( lit2, lit1 ) )
          val nformula = prim.formula.asInstanceOf[FOLFormula].renameSymbols( smap )

          val inference = Paramodulation( rparent1, rparent2, rmap1( lit1 ), rmap2( lit2 ), nformula, nsub )
          val rmap = rmap1 ++ rmap2

          def matcher( o: FormulaOccurrence, t: FormulaOccurrence ): Boolean = {
            //println("anc matcher")
            //println(o); println(o.ancestors)
            //println(t); println(t.ancestors)
            val anc_correspondences: Seq[FormulaOccurrence] = o.parents.map( rmap )
            //println(anc_correspondences)
            t.formula == o.formula.asInstanceOf[FOLFormula].renameSymbols( smap ) &&
              anc_correspondences.diff( t.parents ).isEmpty &&
              t.parents.diff( anc_correspondences ).isEmpty
          }

          val rsmap = find_matching( clause.negative.toList, inference.root.negative.toList, matcher ) ++
            find_matching( clause.positive.toList, inference.root.positive.toList, matcher )

          extendw_pmap( p, rpmap2, rsmap, inference )

      }
  }

  /* creates a mapping from elements in objects to targets. the predicate matches indicates when two elements should
     be considered to match each */
  def find_matching[A, B]( objects: List[A], targets: List[B], matches: ( A, B ) => Boolean ): Map[A, B] = {
    objects match {
      case x :: xs =>
        val ( prefix, suffix ) = targets.span( !matches( x, _ ) )
        suffix match {
          case el :: rest => find_matching( xs, prefix ++ rest, matches ) + ( ( x, el ) )
          case Nil        => throw new Exception( "Can not find a match for element " + x + " in " + targets )
        }

      case Nil =>
        if ( targets.isEmpty )
          Map[A, B]()
        else
          throw new Exception( "Want to create a matching of sets of different size! remaining elements: " + targets )
    }
  }

}
