/*
 * projections.scala
 *
 */

package at.logic.transformations.ceres.projections

import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}
import scala.collection.immutable.HashSet
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.{rename,freeVariables}
import at.logic.calculi.lksk.{ExistsSkLeftRule, ForallSkRightRule, ExistsSkRightRule, ForallSkLeftRule, 
                              WeakeningLeftRule => WeakeningSkLeftRule, WeakeningRightRule => WeakeningSkRightRule,
                              Axiom => AxiomSk, LabelledFormulaOccurrence}
import at.logic.calculi.lksk.TypeSynonyms._

case class ProjectionException(message : String, original_proof: LKProof, new_proofs : List[LKProof], nested : Exception)
  extends Exception(message, nested) { }

object Projections extends at.logic.utils.logging.Logger {
 
  def reflexivity_projection( proof:LKProof, t : TA = Ti) : LKProof = {
    //TODO: in case of fol, fol equality is not used
    //TODO: lksk is not handled
    val es = proof.root.toFSequent
    val x = es.formulas.headOption match {
      case Some(f) => f.factory.createVar(StringSymbol("x"), t)
      case None => HOLVar(StringSymbol("x"), t)
    }

    var count = 0
    val x_ = rename(x, es.formulas.flatMap(freeVariables(_)).toList).asInstanceOf[HOLVar]
    val ax : LKProof = Axiom(Nil, List(Equation(x_,x_)))
    val left = es.antecedent.foldLeft(ax)( (p, f) => WeakeningLeftRule(p,f))
    val right = es.succedent.foldLeft(left)( (p, f) => WeakeningRightRule(p,f))
    right
  }

  def lksk_reflexivity_projection( proof:LKProof, t : TA = Ti) : LKProof = {

    //TODO: in case of fol, fol equality is not used
    val es = proof.root.toFSequent
    val x = es.formulas.headOption match {
      case Some(f) => f.factory.createVar(StringSymbol("x"), t)
      case None => HOLVar(StringSymbol("x"), t)
    }

    var count = 0
    val x_ = rename(x, es.formulas.flatMap(freeVariables(_)).toList).asInstanceOf[HOLVar]
    val (ax,_) = AxiomSk.createDefault(
      FSequent(Nil, List(Equation(x_,x_))),
      (List(), List(EmptyLabel()))
    )
    require(ax.root.occurrences.size == 1, "Couldn't create reflexivity!")
    val left = es.antecedent.foldLeft(ax)( (p, f) => WeakeningSkLeftRule.createDefault(p,f,EmptyLabel()))
    val right = es.succedent.foldLeft(left)( (p, f) => WeakeningSkRightRule.createDefault(p,f,EmptyLabel()))
    require(right.root.occurrences.size == es.formulas.size + 1, "Size of end-sequent is wrong!")
    right
  }

  // This method computes the standard projections according to the original CERES definition.
  def apply( proof: LKProof ) : Set[LKProof] = apply(proof, Set.empty[FormulaOccurrence], x => true)
  def apply( proof: LKProof, pred : HOLFormula => Boolean ) : Set[LKProof] = apply(proof, Set.empty[FormulaOccurrence], pred)

  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence], pred : HOLFormula => Boolean) : Set[LKProof] = {
    implicit val c_ancs = cut_ancs
    try {
      debug("working on rule "+proof.rule)
    
    proof match {
      case Axiom(s) => Set(Axiom(s))

      case ExistsSkLeftRule(p,_,a,m,v) => handleLKSKStrongQuantRule( proof, p, a, m, v, ExistsSkLeftRule.apply, pred )
      case ForallSkRightRule(p,_,a,m,v) => handleLKSKStrongQuantRule( proof, p, a, m, v, ForallSkRightRule.apply, pred )
      case ExistsSkRightRule(p,_,a,m,t) => handleLKSKWeakQuantRule( proof, p, a, m, t, ExistsSkRightRule.apply, pred )
      case ForallSkLeftRule(p,_,a,m,t) => handleLKSKWeakQuantRule( proof, p, a, m, t, ForallSkLeftRule.apply, pred )
      case WeakeningSkLeftRule(p,_, m) => handleLKSKWeakeningRule( proof, p, m, WeakeningSkLeftRule.createDefault, pred )
      case WeakeningSkRightRule(p,_, m) => handleLKSKWeakeningRule( proof, p, m, WeakeningSkRightRule.createDefault, pred )

      case ForallRightRule(p,_, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ForallRightRule.apply, pred )
      case ExistsLeftRule(p,_, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ExistsLeftRule.apply, pred )
      case AndRightRule(p1, p2,_, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, AndRightRule.apply, pred )
      case OrLeftRule(p1, p2,_, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, OrLeftRule.apply, pred )
      case ImpLeftRule(p1, p2,_, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, ImpLeftRule.apply, pred )
      case ForallLeftRule(p,_, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ForallLeftRule.apply, pred )
      case ExistsRightRule(p,_, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ExistsRightRule.apply, pred )
      case NegLeftRule( p,_, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.apply, pred )
      case NegRightRule( p,_, a, m ) => handleNegRule( proof, p, a, m, NegRightRule.apply, pred )
      case ContractionLeftRule(p,_, a1, a2, m) => handleContractionRule( proof, p, a1, a2, m, ContractionLeftRule.apply, pred)
      case ContractionRightRule(p,_, a1, a2, m) => handleContractionRule( proof, p, a1, a2, m, ContractionRightRule.apply, pred)
      case OrRight1Rule(p,_, a, m) => handleUnaryRule( proof, p, a,
        m.formula match { case Or(_, w) => w }, m, OrRight1Rule.apply, pred)
      case OrRight2Rule(p,_, a, m) => handleUnaryRule( proof, p,
        a, m.formula match { case Or(w, _) => w }, m, flipargs(OrRight2Rule.apply), pred)
      case AndLeft1Rule(p,_, a, m) => handleUnaryRule( proof, p, a,
        m.formula match { case And(_, w) => w }, m, AndLeft1Rule.apply, pred)
      case AndLeft2Rule(p,_, a, m) => handleUnaryRule( proof, p,
        a, m.formula match { case And(w, _) => w }, m, flipargs(AndLeft2Rule.apply), pred)
      case ImpRightRule(p,_, a1, a2, m) => handleUnaryImpRule(proof, p, a1,a2, m, ImpRightRule.apply, pred)
      case WeakeningLeftRule(p,_, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply , pred)
      case WeakeningRightRule(p,_, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply , pred)
      case DefinitionLeftRule( p,_, a, m ) => handleDefRule( proof, p, a, m, DefinitionLeftRule.apply , pred)
      case DefinitionRightRule( p,_, a, m ) => handleDefRule( proof, p, a, m, DefinitionRightRule.apply , pred)
      case EquationLeft1Rule( p1, p2,_, e, a,_, m ) => handleEqRule( proof, p1, p2, e, a, m, EquationLeftMacroRule.apply , pred)
      case EquationLeft2Rule( p1, p2,_, e, a,_, m ) => handleEqRule( proof, p1, p2, e, a, m, EquationLeftMacroRule.apply , pred)
      case EquationRight1Rule( p1, p2,_, e, a,_, m ) => handleEqRule( proof, p1, p2, e, a, m, EquationRightMacroRule.apply , pred)
      case EquationRight2Rule( p1, p2,_, e, a,_, m ) => handleEqRule( proof, p1, p2, e, a, m, EquationRightMacroRule.apply , pred)
      case CutRule( p1, p2,_, a1, a2 ) =>
      if (pred(a1.formula)) {
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val s1 = apply( p1, new_cut_ancs + a1, pred )
        val s2 = apply( p2, new_cut_ancs + a2, pred )
        handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs + a1 + a2 )
      } else {
        val new_cut_ancs = copySetToAncestor( cut_ancs )
        val s1 = apply( p1, new_cut_ancs, pred )
        val s2 = apply( p2, new_cut_ancs, pred )
        s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
          s ++ s2.map( p2 =>
          {
            val List(aux1,aux2) = pickrule(proof, List(p1.root,p2.root), List(a1, a2))
            CutRule( p1, p2, aux1, aux2 )
          }))      }
      case _ => throw new Exception("No such a rule in Projections.apply")
    }
    } catch {
      case e : ProjectionException =>
        //println("passing exception up...")
        //throw ProjectionException(e.getMessage, proof, Nil, null)
        throw e
      case e : Exception =>
        throw ProjectionException("Error computing projection: "+e.getMessage+"\n"+e.getStackTrace, proof, Nil, e)
    }
  }

  //flips parameters of unary object constructors s.t. they have the same signature
  def flipargs[A,B,C,D](f : (A,B,C) => D ) : ((A,C,B) => D) = (a:A, c:C, b:B) => f(a,b,c)

  //picks one occurrences from the candidates s.t. formula and skolem label (if it exists) are identical
  def pick(aux : FormulaOccurrence, candidates : Seq[FormulaOccurrence]) : FormulaOccurrence = pick1(aux,candidates)._1

  def pick1(aux : FormulaOccurrence, candidates : Seq[FormulaOccurrence]) : (FormulaOccurrence, Seq[FormulaOccurrence]) = {
    val pred = aux match {
      case a:LabelledFormulaOccurrence =>
        (x:FormulaOccurrence) => x.isInstanceOf[LabelledFormulaOccurrence] &&
                               x.formula == a.formula &&
                               x.asInstanceOf[LabelledFormulaOccurrence].skolem_label == a.skolem_label
      case _ =>
        (x:FormulaOccurrence) => x.formula == aux.formula
    }
    try {
      partitionFirst(pred, candidates)
    } catch {
      case e:Exception => throw new Exception("Can not find suitable occurrence for "+aux+" in "+candidates.mkString("{",",","}"),e)
    }
  }

  //picks 2 occurrences from the same list s.t. ac1 != ac2, where formulas and skolem label agree
  def pick2(aux1 : FormulaOccurrence, aux2 : FormulaOccurrence, candidates : Seq[FormulaOccurrence]) = {
    //debug("Picking "+aux1+" and "+aux2+" from "+candidates.mkString("{",",","}"))
    val (ac1, candidates2) = pick1(aux1, candidates)
    require(! candidates2.contains(ac1), "Occurrence of "+ac1+" may not be contained in "+candidates2)
    val (ac2,_) = pick1(aux2, candidates2 )
    require(ac1 != ac2, "Need to pick different occurrences!")
    List(ac1, ac2)
  }

  def pickrule(p: LKProof, s:List[Sequent], aux : List[FormulaOccurrence]) : List[FormulaOccurrence] = {
    //debug("Pick for rule: "+p.name)
    p.rule match {
      //Unary rules
      case WeakeningLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case WeakeningRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))
      case ContractionLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        pick2(aux(0), aux(1), s(0).antecedent)
      case ContractionRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        pick2(aux(0), aux(1), s(0).succedent)

      case NegLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))
      case NegRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case AndLeft1RuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case AndLeft2RuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case OrRight1RuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))
      case OrRight2RuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))
      case ImpRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).antecedent), pick(aux(1), s(0).succedent))
      case DefinitionLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case DefinitionRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))

      case ForallLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case ForallRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))
      case ExistsLeftRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).antecedent))
      case ExistsRightRuleType =>
        require(s.nonEmpty, "Unary rule needs at least one sequent for lookup!")
        require(aux.nonEmpty, p.name + " rule needs at least one aux formula for lookup!")
        List(pick(aux(0), s(0).succedent))

      //TODO: lksk rules

      //Binary rules
      case CutRuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).antecedent))
      case OrLeftRuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).antecedent), pick(aux(1), s(1).antecedent))
      case AndRightRuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).succedent))
      case ImpLeftRuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).antecedent))
      case EquationLeft1RuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).antecedent))
      case EquationLeft2RuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).antecedent))
      case EquationRight1RuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).succedent))
      case EquationRight2RuleType =>
        require(s.size >= 2, "Binary rule needs at least two sequents for lookup!")
        require(aux.size >= 2, p.name + " rule needs at least two aux formulas for lookup!")
        List(pick(aux(0), s(0).succedent), pick(aux(1), s(1).succedent))
    }

  }

  private def partitionFirst[A](pred: A=> Boolean, s:Seq[A]) : (A, Seq[A]) = {
    if (s.isEmpty) throw new Exception("No fitting formula found!")
    else if (pred(s.head) ) (s.head, s.tail)
    else {
      val (e, rs) = partitionFirst(pred, s.tail)
      (e, s.head +: rs)
    }

  }


  def handleBinaryESAnc( proof: LKProof with AuxiliaryFormulas, parent1: LKProof, parent2: LKProof, s1: Set[LKProof], s2: Set[LKProof],
                         constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) =
    s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
      s ++ s2.map( p2 =>  //try
      {
        val List(a1,a2) = pickrule(proof, List(p1.root,p2.root), List(proof.aux(0)(0), proof.aux(1)(0)))
        constructor( p1, p2, a1, a2 )
//      } catch {
//        case e:Exception => throw ProjectionException("binary end-sequent ancestor rule failed: ", proof, p1::p2::Nil, e)
      }
     ) )

  def getESAncs( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) =
    ( proof.root.antecedent.filter( fo => !cut_ancs.contains( fo ) ),
          proof.root.succedent.filter( fo => !cut_ancs.contains( fo ) ) )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof, s1: Set[LKProof], s2: Set[LKProof], cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs ), s2 )
    new_p1 ++ new_p2
  }

  // Apply weakenings to add the end-sequent ancestor of the other side to the projection.
  def weakenESAncs( esancs: Tuple2[Seq[FormulaOccurrence], Seq[FormulaOccurrence]], s: Set[LKProof] ) = {
    val wl = s.map( p => esancs._1.foldLeft( p )( (p, fo) => fo match {
        case locc : LabelledFormulaOccurrence =>
          //in lksk we must add the correct label
          WeakeningSkLeftRule.createDefault(p, locc.formula, locc.skolem_label)
        case _ =>
          WeakeningLeftRule( p, fo.formula )
      }) )
    wl.map( p => esancs._2.foldLeft( p )( (p, fo) => fo match {
      case locc : LabelledFormulaOccurrence =>
        //in lksk we must add the correct label
        WeakeningSkRightRule.createDefault(p, locc.formula, locc.skolem_label)
      case _ =>
        WeakeningRightRule( p, fo.formula )
    } ) )
  }

  def handleContractionRule( proof: LKProof, p: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m: FormulaOccurrence,
                             constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof,
                             pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => {
      val List(a1_,a2_) = pickrule(proof, List(pm.root), List(a1,a2))
      constructor( pm, a1_, a2_)
    })
  }

  def handleUnaryRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, w: HOLFormula, m: FormulaOccurrence,
                       constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof,
                       pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred)
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => {
      val List(a_) = pickrule(proof, List(pm.root), List(a))
      constructor( pm, a_, w )
    } )
  }

  //implication does not weaken the second argument, we need two occs
  def handleUnaryImpRule( proof: LKProof, p: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m: FormulaOccurrence,
                       constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof,
                       pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => {
      val List(a1_,a2_) = pickrule(proof, List(pm.root), List(a1,a2))
      constructor( pm, a1_, a2_ )
    })
  }

  def handleWeakeningRule( proof: LKProof, p: LKProof, m: FormulaOccurrence,
                           constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                           pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => constructor( pm, m.formula ) )
  }

  def handleLKSKWeakeningRule( proof: LKProof, p: LKProof, m: LabelledFormulaOccurrence,
                               constructor: (LKProof, HOLFormula, Label) => LKProof with PrincipalFormulas,
                               pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else {
      s.map( pm => constructor( pm, m.formula, m.skolem_label ) )
    }
  }

  def handleDefRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
                     constructor: (LKProof, FormulaOccurrence, HOLFormula) => LKProof,
                     pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => {
      val List(a_) = pickrule(proof, List(pm.root), List(a))
      constructor( pm, a_, m.formula )
    } )
  }

  def handleNegRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence,
                     constructor: (LKProof, FormulaOccurrence) => LKProof,
                     pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else s.map( pm => {
      val List(a_) = pickrule(proof, List(pm.root), List(a))
      constructor( pm, a_ )
    } )
  }

  def handleWeakQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, t: HOLExpression,
                           constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof,
                           pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains(m)) s
    else s.map( pm => {
      val List(a_) = pickrule(proof, List(pm.root), List(a))
      constructor( pm, a_, m.formula, t)
    })
  }

  def handleLKSKWeakQuantRule( proof: LKProof, p: LKProof, a: LabelledFormulaOccurrence, m: LabelledFormulaOccurrence, t: HOLExpression,
                               constructor: (LKProof, LabelledFormulaOccurrence, HOLFormula, HOLExpression, Boolean) => LKProof,
                               pred : HOLFormula => Boolean)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains(m)) s
    else {
      require(p.root.occurrences.contains(a), "Error projecting a lksk Weak Quantifier rule! Auxiliary formula not contained in parent!")
      val in_antecedent = p.root.antecedent.contains(a)

      val set = s.map( pm => {
        //TODO: check label
        val r = if (in_antecedent) {
          pm.root.antecedent.find(lo => lo.formula == a.formula)
        } else {
          pm.root.succedent.find(lo => lo.formula == a.formula)
        }

        val label_removed = m.skolem_label.diff(a.skolem_label).nonEmpty || a.skolem_label.diff(m.skolem_label).nonEmpty
        //if (label_removed) println("label was removed ")//+a.skolem_label.diff(m.skolem_label).mkString(","))
        //else println("keeping label!"+m.skolem_label.mkString(","))

        r match {
          case Some(auxf) =>
            constructor( pm, auxf.asInstanceOf[LabelledFormulaOccurrence], m.formula, t, label_removed)
          case _ =>
            throw new Exception("Error projecting a lksk Weak Quantifier rule! Could not find auxformula in projection parent!")
        }
      }
      )
      set
    }
  }


  def handleBinaryRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
                        m: FormulaOccurrence, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof,
                        pred : HOLFormula => Boolean)( implicit cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs, pred )
    val s2 = apply( p2, new_cut_ancs, pred )
    //println("Binary rule on:\n"+s1.map(_.root)+"\n"+s2.map(_.root))
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      handleBinaryESAnc( proof.asInstanceOf[LKProof with AuxiliaryFormulas], p1, p2, s1, s2, constructor )
  }

  def handleEqRule( proof: LKProof, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
                    m: FormulaOccurrence, constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof,
                    pred : HOLFormula => Boolean)( implicit cut_ancs: Set[FormulaOccurrence]) = {
    val new_cut_ancs = copySetToAncestor( cut_ancs )
    val s1 = apply( p1, new_cut_ancs, pred )
    val s2 = apply( p2, new_cut_ancs, pred )
    if ( cut_ancs.contains( m ) )
      handleBinaryCutAnc( proof, p1, p2, s1, s2, new_cut_ancs )
    else
      s1.foldLeft( Set.empty[LKProof] )( (s, p1) =>
        s ++ s2.map( p2 => {
          val List(a1_,a2_) = pickrule(proof, List(p1.root, p2.root), List(a1,a2))
          constructor( p1, p2, a1_, a2_, m.formula )
        } )
      )
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, v: HOLVar,
                             constructor: (LKProof, HOLFormula, HOLFormula, HOLVar) => LKProof, pred : HOLFormula => Boolean)( implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains( m ) ) s
    else throw new Exception("The proof is not skolemized!") // s.map( p => constructor( p, a, m.formula, v ) )
  }

  def handleLKSKStrongQuantRule( proof: LKProof, p: LKProof, a: LabelledFormulaOccurrence, m: LabelledFormulaOccurrence, skolemterm: HOLExpression,
                                 constructor: (LKProof, LabelledFormulaOccurrence, HOLFormula, HOLExpression) => LKProof,
                                 pred : HOLFormula => Boolean)( implicit cut_ancs: Set[FormulaOccurrence]) : Set[LKProof] = {
    val s = apply( p, copySetToAncestor( cut_ancs ), pred )
    if (cut_ancs.contains(m)) s
    else {
      require(p.root.occurrences.contains(a), "Error projecting a lksk Weak Quantifier rule! Auxiliary formula not contained in parent!")
      val in_antecedent = p.root.antecedent.contains(a)

      val set = s.map( pm => {
        //TODO: check label
        val r = if (in_antecedent) {
          pm.root.antecedent.find(lo => lo.formula == a.formula)
        } else {
          pm.root.succedent.find(lo => lo.formula == a.formula)
        }


        r match {
          case Some(auxf) =>
            constructor( pm, auxf.asInstanceOf[LabelledFormulaOccurrence], m.formula, skolemterm)
          case _ =>
            throw new Exception("Error projecting a lksk Weak Quantifier rule! Could not find auxformula in projection parent!")
        }
      }
      )
      set
    }
  }

  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.parents )
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
    val setant = s.antecedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    val setsucc = s.succedent.map(fo => fo.formula).toSet.foldLeft(Seq.empty[HOLFormula])((seq, t) => t +: seq)
    Sequent(setant.map(f => factory.createFormulaOccurrence(f, Nil)), setsucc.map(f => factory.createFormulaOccurrence(f, Nil)))
  }
}

object DeleteRedundantSequents {
  private def member(seq : Sequent, l : List[Sequent]): Boolean = {
    l match {
      case seq1::ls =>
        if (seq.antecedent.toList.map(fo => fo.formula).toSet == seq1.antecedent.toList.map(fo => fo.formula).toSet &&
          seq.succedent.toList.map(fo => fo.formula).toSet == seq1.succedent.toList.map(fo => fo.formula).toSet
        ) true
        else member(seq, ls)
      case _ => false
    }
  }

  def apply(l : List[Sequent]): List[Sequent] = {
    l match {
      case x::ls =>
        val new_ls = apply(ls)
        if (member(x, new_ls))
          new_ls
        else
          x::new_ls
      case _ => List[Sequent]()
    }
  }
}

