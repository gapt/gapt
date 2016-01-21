package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.occurrences._

/**
 * The pick* functions generalize the convenience constructors of the LK rules which allow to specify arguments by
 * a formula instead of an index. Here we lookup fitting matches for the auxiliary formulas of each LK rule.
 * In the case of LK, fitting is defined as equality of the formula. In the case of LKsk, it is equality of formulas
 * and skolem symbols. An algorithm using pickrule is therefore easier to transfer to LKsk.
 */
//TODO: generalize the definition of fitting (add a predicate which decides if a candidate fits)
object Pickrule {
  type zipIndex = ( HOLFormula, SequentIndex )

  /**
   * picks one occurrences from the candidates s.t. formulas (if it exists) are identical
   *
   * @param p the proof which is used as template
   * @param aux an index into p.endSequent
   * @param candidates a list of candidate formulas to pick a match for aux
   * @return the index of a fitting formulas for aux
   */
  def pick( p: LKProof, aux: SequentIndex, candidates: Seq[zipIndex] ): SequentIndex =
    pick1( p.endSequent, aux, candidates )._1

  /**
   * picks one occurrences from the candidates s.t. formulas (if it exists) are identical.
   * @return the index of a fitting formulas for aux
   */
  def pick( es: HOLSequent, aux: SequentIndex, candidates: Seq[zipIndex] ): SequentIndex =
    pick1( es, aux, candidates )._1

  /**
   * picks 2 occurrences from the same list s.t. ac1 != ac2, where formulas and skolem label agree
   * @return a list with the indices of a fitting formulas for aux1 / aux2
   */
  def pick2( p: LKProof, aux1: SequentIndex, aux2: SequentIndex, candidates: Seq[zipIndex] ): List[SequentIndex] =
    pick2( p.endSequent, aux1, aux2, candidates )

  /**
   * picks 2 occurrences from the same list s.t. ac1 != ac2, where formulas and skolem label agree
   * @return a list with the indices of a fitting formulas for aux1 / aux2
   */
  def pick2( es: HOLSequent, aux1: SequentIndex, aux2: SequentIndex, candidates: Seq[zipIndex] ): List[SequentIndex] = {
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
  def pick1( es: HOLSequent, aux: SequentIndex, candidates: Seq[zipIndex] ): ( SequentIndex, Seq[zipIndex] ) = {
    val auxformula = es( aux )
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
  def pickrule( p: LKProof, old_parents: Seq[LKProof], new_parents: Seq[LKProof], old_aux: List[SequentIndex] ): List[SequentIndex] = {
    //debug("Pick for rule: "+p.name)
    val s = new_parents map ( _.endSequent.zipWithIndex )
    p match {
      //Unary rules
      case _: WeakeningLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: WeakeningRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: ContractionLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).antecedent )
      case _: ContractionRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).succedent )

      case _: NegLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: NegRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: AndLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least one old_aux formula for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).antecedent )
      case _: OrRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least one old_aux formula for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).succedent )
      case _: ImpRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List(
          pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ),
          pick( old_parents( 0 ), old_aux( 1 ), s( 0 ).succedent )
        )
      case _: DefinitionLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: DefinitionRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: ForallLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: ForallRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )
      case _: ExistsLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ) )
      case _: ExistsRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ) )

      case _: EqualityLeftRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        pick2( old_parents( 0 ), old_aux( 0 ), old_aux( 1 ), s( 0 ).antecedent )
      case _: EqualityRightRule =>
        require( s.nonEmpty, "Unary rule needs at least one sequent for lookup!" )
        require( old_aux.nonEmpty, p.name + " rule needs at least one old_aux formula for lookup!" )
        List(
          pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ),
          pick( old_parents( 0 ), old_aux( 1 ), s( 0 ).succedent )
        )

      //Binary rules
      case _: CutRule =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).antecedent ) )
      case _: OrLeftRule =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).antecedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).antecedent ) )
      case _: AndRightRule =>
        require( s.size >= 2, "Binary rule needs at least two sequents for lookup!" )
        require( old_aux.size >= 2, p.name + " rule needs at least two old_aux formulas for lookup!" )
        List( pick( old_parents( 0 ), old_aux( 0 ), s( 0 ).succedent ), pick( old_parents( 1 ), old_aux( 1 ), s( 1 ).succedent ) )
      case _: ImpLeftRule =>
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

//TODO: change to new lk
object DeleteReduntantFOfromSequent {
  def apply( s: OccSequent ): OccSequent = {
    val setant = s.antecedent.map( fo => fo.formula ).toSet.foldLeft( Seq.empty[HOLFormula] )( ( seq, t ) => t +: seq )
    val setsucc = s.succedent.map( fo => fo.formula ).toSet.foldLeft( Seq.empty[HOLFormula] )( ( seq, t ) => t +: seq )
    OccSequent( setant.map( f => factory.createFormulaOccurrence( f, Nil ) ), setsucc.map( f => factory.createFormulaOccurrence( f, Nil ) ) )
  }
}

//TODO: change to new lk
object DeleteRedundantSequents {
  private def member( seq: OccSequent, l: List[OccSequent] ): Boolean = {
    l match {
      case seq1 :: ls =>
        if ( seq.antecedent.toList.map( fo => fo.formula ).toSet == seq1.antecedent.toList.map( fo => fo.formula ).toSet &&
          seq.succedent.toList.map( fo => fo.formula ).toSet == seq1.succedent.toList.map( fo => fo.formula ).toSet ) true
        else member( seq, ls )
      case _ => false
    }
  }

  def apply( l: List[OccSequent] ): List[OccSequent] = {
    l match {
      case x :: ls =>
        val new_ls = apply( ls )
        if ( member( x, new_ls ) )
          new_ls
        else
          x :: new_ls
      case _ => List[OccSequent]()
    }
  }
}

