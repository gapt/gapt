package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.proofs.occurrences._

/**
 * The pick* functions generalize the convenience constructors of the LK rules which allow to specify arguments by
 * a formula instead of an index. Here we lookup fitting matches for the auxiliary formulas of each LK rule.
 * In the case of LK, fitting is defined as equality of the formula. In the case of LKsk, it is equality of formulas
 * and skolem labels. An algorithm using pickrule is therefore easier to transfer to LKsk.
 */
//TODO: generalize the definition of fitting (add a predicate which decides if a candidate fits)
object Pickrule {
  type zipIndex = ( LabelledFormula, SequentIndex )

  /**
   * picks one occurrences from the candidates s.t. formulas (if it exists) are identical
   *
   * @param p the proof which is used as template
   * @param aux an index into p.endSequent
   * @param candidates a list of candidate formulas to pick a match for aux
   * @return the index of a fitting formulas for aux
   */
  def pick( p: LKskProof, aux: SequentIndex, candidates: Seq[zipIndex] ): SequentIndex =
    pick1( p.conclusion, aux, candidates )._1

  /**
   * picks one occurrences from the candidates s.t. formulas (if it exists) are identical.
   * @return the index of a fitting formulas for aux
   */
  def pick( es: LabelledSequent, aux: SequentIndex, candidates: Seq[zipIndex] ): SequentIndex =
    pick1( es, aux, candidates )._1

  /**
   * picks 2 occurrences from the same list s.t. ac1 != ac2, where formulas and skolem label agree
   * @return a list with the indices of a fitting formulas for aux1 / aux2
   */
  def pick2( p: LKskProof, aux1: SequentIndex, aux2: SequentIndex, candidates: Seq[zipIndex] ): List[SequentIndex] =
    pick2( p.conclusion, aux1, aux2, candidates )

  /**
   * picks 2 occurrences from the same list s.t. ac1 != ac2, where formulas and skolem label agree
   * @return a list with the indices of a fitting formulas for aux1 / aux2
   */
  def pick2( es: LabelledSequent, aux1: SequentIndex, aux2: SequentIndex, candidates: Seq[zipIndex] ): List[SequentIndex] = {
    //debug("Picking "+aux1+" and "+aux2+" from "+candidates.mkString("{",",","}"))
    val ( ac1, candidates2 ) = pick1( es, aux1, candidates )
    val ( ac2, _ ) = pick1( es, aux2, candidates2 )
    require( ac1 != ac2, "Need to pick different occurrences!" )
    List( ac1, ac2 )
  }

  /**
   * picks 1 occurrence from the same list s.t. ac1 != ac2, where formulas and skolem label agree
   * @return a pair of index and remaining candidates
   */
  def pick1( es: LabelledSequent, aux: SequentIndex, candidates: Seq[zipIndex] ): ( SequentIndex, Seq[zipIndex] ) = {
    val auxformula = es( aux )
    //TODO: add restriction to es-ancestor
    candidates.find( _._1 == auxformula ) match {
      case Some( ( _, index ) ) => ( index, candidates filterNot ( _._2 == index ) )
      case None                 => throw new Exception( "Can not find suitable occurrence for " + auxformula + " in " + candidates.toString )
    }
  }

  /**
   * For a rule p with parent sequents ps and auxiliary formulas aux, pick a fitting formula for each aux
   * formula in the correct part of the sequent. E.g. if p is an implication right rule, aux(0) will be picked
   * from the antecedent of ps(0) and aux(1) will be picked from the succedent of ps(0).
   *
   * @param p The proof which rule should be simulated, we assume we want to mirror the inference to create a similar proof p'
   * @param old_parents The parents of p.
   * @param new_parents The intended parents for p'
   * @param old_aux The indices of the auxiliary formulas in the parents
   * @return a list of indices in new_parents where the formulas match old_aux
   */
  def pickrule( p: LKskProof, old_parents: Seq[LKskProof], new_parents: Seq[( LKskProof, Sequent[Boolean] )],
                old_aux: List[SequentIndex] ): List[SequentIndex] = {
    //debug("Pick for rule: "+p.name)
    //TODO: adapt for additional exclusion list
    val s = new_parents map ( _._1.conclusion.zipWithIndex )
    p match {
      //Unary rules
      case _: WeakeningLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: WeakeningRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: ContractionLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).antecedent )
      case _: ContractionRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).succedent )

      case _: NegLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: NegRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: AndLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least one old_aux formula for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).antecedent )
      case _: OrRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least one old_aux formula for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).succedent )
      case _: ImpRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List(
          pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ),
          pick( old_parents( 0 ), old_aux( 1 ), s( 0 ).succedent )
        )
      case _: AllLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: AllRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: ExLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: ExRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      /*
      case _: EqualityLeft =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: EqualityRight =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
*/
      //Binary rules
      case _: Cut =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).antecedent ) )
      case _: OrLeft =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).antecedent ) )
      case _: AndRight =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).succedent ) )
      case _: ImpLeft =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).antecedent ) )

    }

  }
}

object DeleteTautology {
  def apply( l: List[HOLSequent] ): List[HOLSequent] = apply( l, ( x: HOLFormula, y: HOLFormula ) => x == y )
  //def apply( l : List[OccSequent]) = apply(l, (x : FormulaOccurrence,y:FormulaOccurrence) => x.formula == y.formula )

  def apply[A]( l: List[Sequent[A]], eqpred: ( A, A ) => Boolean ): List[Sequent[A]] = {
    l.filterNot( seq => {
      seq.antecedent.exists( x =>
        seq.succedent.exists( y => eqpred( x, y ) ) )
    } )
  }
}