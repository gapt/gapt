package at.logic.transformations.ceres.projections

/*
 * projections.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}
import scala.collection.immutable.HashSet

object Projections {
  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKProof ) : Set[LKProof] = apply(proof, Set.empty[FormulaOccurrence])

  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    implicit val c_ancs = cut_ancs
    implicit val factory = defaultFormulaOccurrenceFactory
    proof match {
      case Axiom(s) => Set(Axiom(s))
      case ForallRightRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a.formula, m, v, ForallRightRule.apply )
      case ExistsLeftRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a.formula, m, v, ExistsLeftRule.apply )
      case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, AndRightRule.apply )
      case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, OrLeftRule.apply )
      case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1.formula, a2.formula, m, ImpLeftRule.apply )
      case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a.formula, m, t, ForallLeftRule.apply )
      case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a.formula, m, t, ExistsRightRule.apply )
      case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a.formula, m, NegLeftRule.apply )
      case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a.formula, m, NegRightRule.apply )
      case ContractionLeftRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1.formula, a2.formula, m, ContractionLeftRule.apply)
      case ContractionRightRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1.formula, a2.formula, m, ContractionRightRule.apply)
      case OrRight1Rule(p, _, a, m) => handleUnaryRule( proof, p, a.formula,
        m.formula match { case Or(_, w) => w }, m, OrRight1Rule.apply)
      case OrRight2Rule(p, _, a, m) => handleUnaryRule( proof, p,
        m.formula match { case Or(w, _) => w }, a.formula, m, OrRight2Rule.apply)
      case AndLeft1Rule(p, _, a, m) => handleUnaryRule( proof, p, a.formula,
        m.formula match { case And(_, w) => w }, m, AndLeft1Rule.apply)
      case AndLeft2Rule(p, _, a, m) => handleUnaryRule( proof, p,
        m.formula match { case And(w, _) => w }, a.formula, m, AndLeft2Rule.apply)
      case ImpRightRule(p, _, a1, a2, m) => handleUnaryRule(proof, p, a1.formula, a2.formula, m, ImpRightRule.apply)
      case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply )
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply )
      case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a.formula, m, DefinitionLeftRule.apply )
      case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a.formula, m, DefinitionRightRule.apply )
      case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationLeft1Rule.apply )
      case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationLeft2Rule.apply )
      case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationRight1Rule.apply )
      case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e.formula, a.formula, m, EquationRight2Rule.apply )
      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val s1 = apply( p1, new_cut_ancs + a1 )
        val s2 = apply( p2, new_cut_ancs + a2 )
        handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs + a1 + a2 )
      }
      case _ => throw new Exception("No such a rule in Projections.apply")
    }
  }

  def handleBinaryESAnc( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, s1: Set[LKProof], s2: Set[LKProof],
    constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof) =
    s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
      s ++ s2.map( p2 => constructor( p1, p2, proof.aux.head.head.formula, proof.aux.tail.head.head.formula ) ) )

  def getESAncs( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) =
    Pair( proof.root.antecedent.filter( fo => !cut_ancs.contains( fo ) ),
          proof.root.succedent.filter( fo => !cut_ancs.contains( fo ) ) )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof, s1: Set[LKProof], s2: Set[LKProof], cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  def weakenESAncs( esancs: Pair[Seq[FormulaOccurrence], Seq[FormulaOccurrence]], s: Set[LKProof] ) = {
    val wl = s.map( p => esancs._1.foldLeft( p )( (p, fo) => WeakeningLeftRule( p, fo.formula ) ) )
    wl.map( p => esancs._2.foldLeft( p )( (p, fo) => WeakeningRightRule( p, fo.formula ) ) )
  }

  def handleContractionRule( proof: LKProof, p: LKProof, a1: HOLFormula, a2: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
    {
      val s = apply( p, copySetToAncestor( cut_ancs ) )
      if (cut_ancs.contains( m ) ) s
      else s.map( pm => constructor( pm, a1) )
    }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: HOLFormula, w: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula, HOLFormula) => LKProof)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a, w ) )
  }

  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, m.formula ) )
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a, m.formula ) )
  }

  def handleNegRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, a ) )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence, t: HOLExpression,
    constructor: (LKProof, HOLFormula, HOLFormula, HOLExpression) => LKProof)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains(m)) s
    else s.map( pm => constructor( pm, a, m.formula, t) )
  }

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: HOLFormula, a2: HOLFormula,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, HOLFormula, HOLFormula) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      handleBinaryESAnc( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: HOLFormula, a2: HOLFormula,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, HOLFormula, HOLFormula, HOLFormula) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
        s ++ s2.map( p2 => constructor( p1, p2, proof.aux.head.head.formula, proof.aux.tail.head.head.formula, m.formula ) )
      )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: HOLFormula, m: FormulaOccurrence, v: HOLVar,
    constructor: (LKProof, HOLFormula, HOLFormula, HOLVar) => LKProof)( implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) ) s
    else throw new Exception("The proof is not skolemized!") // s.map( p => constructor( p, a, m.formula, v ) )
  }

  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )
}

object DeleteTautology {
  def apply(l : List[Sequent]): List[Sequent] = {
    l.filter( seq => {
      seq.antecedent.toList.map(fo => fo.formula).intersect( seq.succedent.toList.map(fo => fo.formula) ) == List[Sequent]()
    } ).map(seq1 => DeleteReduntantFOfromSequent(seq1))
  }
}

object DeleteReduntantFOfromSequent {
  def apply(s : Sequent): Sequent = {
    implicit val factory = defaultFormulaOccurrenceFactory
    val setant = s.antecedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    val setsucc = s.succedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    Sequent(setant.map(f => factory.createFormulaOccurrence(f, Nil)), setsucc.map(f => factory.createFormulaOccurrence(f, Nil)))
  }
}

object DeleteRedundantSequents {
  private def member(seq : Sequent, l : List[Sequent]): Boolean = {
    l match {
      case seq1::ls => {
        if (seq.antecedent.toList.map(fo => fo.formula).toSet == seq1.antecedent.toList.map(fo => fo.formula).toSet &&
            seq.succedent.toList.map(fo => fo.formula).toSet == seq1.succedent.toList.map(fo => fo.formula).toSet
        ) true
        else member(seq, ls)
      }
      case _ => false
    }
  }

  def apply(l : List[Sequent]): List[Sequent] = {
    l match {
      case x::ls => {
        val new_ls = apply(ls)
        if (member(x, new_ls))
          new_ls
        else
          x::new_ls
      }
      case _ => List[Sequent]()
    }
  }
}


// The old code, has a bug in the computation of the mapping!!!
/*
import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}

object Projections {

  // This method computes the standard projections according to the original CERES definition.
  // It also supplies maps from the formula occurrences of the end-sequent of the input proof
  // to those of the projections.
  def apply( proof: LKProof ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = apply( proof, new HashSet[FormulaOccurrence] )

  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = {
    implicit val c_ancs = cut_ancs
    implicit val factory = defaultFormulaOccurrenceFactory

    proof match {
     case Axiom(s) => {
      // TODO: this is also used in the skolemization algorithm. refactor into Axiom.copy( proof )?
      val ant = s.antecedent.toList
      val succ = s.succedent.toList
      val ax = Axiom( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
      var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ant( p._2 ) ))
      new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> succ( p._2 )))

      new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] + Pair(ax, new_map)
    }
      case ForallRightRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ForallRightRule.apply )
      case ExistsLeftRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ExistsLeftRule.apply )
      case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, AndRightRule.apply )
      case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, OrLeftRule.apply )
      case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, ImpLeftRule.apply )
      case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ForallLeftRule.apply )
      case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ExistsRightRule.apply )
      case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.apply )
      case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegRightRule.apply )
      case ContractionLeftRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1, a2, m, ContractionLeftRule.apply)
      case ContractionRightRule(p, _, a1, a2, m) => handleContractionRule( proof, p, a1, a2, m, ContractionRightRule.apply)
      case OrRight1Rule(p, _, a, m) => handleUnaryRule( proof, p, a,
        m.formula match { case Or(_, w) => w }, m, OrRight1Rule.apply)
      case OrRight2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
        m.formula match { case Or(w, _) => w }, m, OrRight2Rule.apply)
      case AndLeft1Rule(p, _, a, m) => handleUnaryRule( proof, p, a,
        m.formula match { case And(_, w) => w }, m, AndLeft1Rule.apply)
      case AndLeft2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
        m.formula match { case And(w, _) => w }, m, AndLeft2Rule.apply)
      case ImpRightRule(p, _, a1, a2, m) => {
        val s = apply( p, copySetToAncestor( cut_ancs ) )
        if (cut_ancs.contains( m ) )
          handleUnaryCutAnc( proof, s )
        else
          s.map( pm => {
            val new_p = ImpRightRule( pm._1, pm._2( a1 ), pm._2( a2 ) )
            (new_p, copyMapToDescendant( proof, new_p, pm._2) )
        } )
      }
      case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply )
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply  )
      case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a, m, DefinitionLeftRule.apply )
      case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a, m, DefinitionRightRule.apply )
      case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e, a, m, EquationLeft1Rule.apply )
      case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e, a, m, EquationLeft2Rule.apply )
      case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e, a, m, EquationRight1Rule.apply )
      case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, e, a, m, EquationRight2Rule.apply )
      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val s1 = apply( p1, new_cut_ancs + a1 )
        val s2 = apply( p2, new_cut_ancs + a2 )
        handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs + a1 + a2 )
      }
    }
  }

  def handleBinaryESAnc( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof,
    s1: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    s2: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) =
  {
    s1.foldLeft( new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] )( (s, p1) =>
      s ++ s2.map( p2 =>
      {
        val new_proof = constructor( p1._1, p2._1, p1._2( proof.aux.head.head ), p2._2( proof.aux.tail.head.head ) )
        val new_map = copyMapToDescendant( proof, new_proof, p1._2 ++ p2._2 )
        (new_proof, new_map)
      })
    )
  }

  def getESAncs( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) =
    Pair( proof.root.antecedent.filter( fo => !cut_ancs.contains( fo ) ).foldLeft(Set.empty[FormulaOccurrence])((s,fo) => s + fo),
          proof.root.succedent.filter( fo => !cut_ancs.contains( fo ) ).foldLeft(Set.empty[FormulaOccurrence])((s,fo) => s + fo) )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof,
    s1: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    s2: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
    copyMapsToDescLeft( proof, weakenESAncs( getESAncs( p2, cut_ancs ), s1 ) ) ++
    copyMapsToDescLeft( proof, weakenESAncs( getESAncs( p1, cut_ancs ), s2 ) )

  // Apply weakenings to add the end-sequent ancestor of the other side
  // to the projection. Update the relevant maps.
  def weakenESAncs( esancs: Pair[Set[FormulaOccurrence], Set[FormulaOccurrence]],
    s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] ) = {
    val wl = s.map( p =>
      esancs._1.foldLeft( p )( (p, fo) => {
      val w = WeakeningLeftRule( p._1, fo.formula )
      val m = copyMapsToDescRight( w, p._2 ) + ( fo -> w.prin.head )
      (w, m)
    } ) )
    wl.map( p =>
      esancs._2.foldLeft( p )( (p, fo) => {
      val w = WeakeningRightRule( p._1, fo.formula )
      val m = copyMapsToDescRight( w, p._2 ) + ( fo -> w.prin.head )
      (w, m)
    } ) )
  }

  def copyMapsToDescRight( proof: LKProof, map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.foldLeft( new HashMap[FormulaOccurrence, FormulaOccurrence] )( (m, p) =>
    {
      val desc = proof.getDescendantInLowerSequent( p._2 )
      if (desc == None)
        m
      else
        m + ( p._1 -> desc.get )
    } )

  def copyMapsToDescLeft( proof: LKProof, s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] ) =
    s.map( pm =>
      ( pm._1, pm._2.foldLeft( new HashMap[FormulaOccurrence, FormulaOccurrence] )( (m, p) =>
      {
        val desc = proof.getDescendantInLowerSequent(p._1)
        if (desc == None)
          m
        else
          m + ( desc.get ->  p._2 )
      } ) ) )

  def handleContractionRule( proof: LKProof, p: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m: FormulaOccurrence,
    constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
    {
      val s = apply( p, copySetToAncestor( cut_ancs ) )
      if (cut_ancs.contains( m ) )
        handleUnaryCutAnc( proof, s )
      else
        s.map( pm => {
          val new_p = constructor( pm._1, pm._2( a1 ), pm._2( a2 ) )
          (new_p, copyMapToDescendant( proof, new_p, pm._2) )
      } )
    }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, w: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
        val new_p = constructor( pm._1, pm._2( a ), w )
        (new_p, copyMapToDescendant( proof, new_p, pm._2) )
    } )
  }

  def handleUnary2Rule( proof: LKProof, p: LKProof, a: FormulaOccurrence, w: HOLFormula, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula, FormulaOccurrence) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
    handleUnaryRule( proof, p, a, w, m, (p, o, f) => constructor(p, f, o) )

  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
    constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
        val new_p = constructor( pm._1, m.formula )
        (new_p, copyMapToDescendant( proof, new_p, pm._2) + ( m -> new_p.prin.head ) )
    } )
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
    constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
        val new_p = constructor( pm._1, pm._2( a ), m.formula )
        (new_p, copyMapToDescendant( proof, new_p, pm._2) )
    } )
  }

  def handleNegRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
    constructor: (LKProof, FormulaOccurrence) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
        val new_p = constructor( pm._1, pm._2( a ) )
        (new_p, copyMapToDescendant( proof, new_p, pm._2) )
    } )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, t: HOLExpression,
    constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof)(implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
    {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
        val new_p = constructor( pm._1, pm._2( a ), m.formula, t )
        (new_p, copyMapToDescendant( proof, new_p, pm._2 ) )
      } )
    }

  // FIXME: why a cast?
  def handleUnaryCutAnc( proof: LKProof, s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] ) =
    copyMapsToDescLeft( proof, s ).asInstanceOf[Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])]]

  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      handleBinaryESAnc( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
    m: FormulaOccurrence, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs )
    val s2 = apply( p2, new_cut_ancs )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      s1.foldLeft( new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] )( (s, p1) =>
        s ++ s2.map( p2 =>
        {
          val new_proof = constructor( p1._1, p2._1, p1._2( proof.aux.head.head ), p2._2( proof.aux.tail.head.head ), m.formula )
          val new_map = copyMapToDescendant( proof, new_proof, p1._2 ++ p2._2 )
          (new_proof, new_map)
        })
      )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, v: HOLVar,
    constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLVar) => LKProof)( implicit
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( p => {
        val new_proof = constructor( p._1, p._2( a ), m.formula, v )
        val new_map = copyMapToDescendant( proof, p._1, p._2 )
        (new_proof, new_map)
      })
  }

  def copyMapsToDescendant( proof: LKProof, s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])]) =
    s.map( p => (p._1, copyMapToDescendant( proof, p._1, p._2 ) ) )

  // TODO: the following 3 are taken from skolemization.scala --- refactor!
  def copyMapToAncestor[A]( map: Map[FormulaOccurrence, A] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, A])( (m, p) => m ++ p._1.ancestors.map( a => (a, p._2) ) )

  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )

  def copyMapToDescendant( old_p: LKProof, new_p: LKProof,
                           map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => {
        val desc = old_p.getDescendantInLowerSequent( p._1 )
        if (desc != None)
          m + (desc.get -> new_p.getDescendantInLowerSequent( p._2 ).get )
        else
          m
      } )
}
  */
