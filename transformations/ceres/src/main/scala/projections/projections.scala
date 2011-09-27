/*
 * projections.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
/*
package at.logic.transformations.ceres.projections

import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
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


/*
 * projections.scala
 *
 * This is the new version including schemata, unfolding and so on...
 */

package at.logic.transformations.ceres.projections

import at.logic.transformations.ceres.struct._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.language.hol._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,PrincipalFormulas}
import at.logic.calculi.slk._
import at.logic.utils.ds.Multisets._
import at.logic.language.schema.{IntVar, IndexedPredicate, SchemaFormula}
import at.logic.calculi.lk.lkExtractors. {BinaryLKProof, UnaryLKProof}
import scala.collection.immutable.Seq


object Projections {

  // This method computes the standard projections according to the original CERES definition.
  // It also supplies maps from the formula occurrences of the end-sequent of the input proof
  // to those of the projections.
  //def apply( proof: LKProof ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = apply( proof, new HashSet[FormulaOccurrence] )

  def apply( proof: LKProof ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = apply( proof, new HashSet[FormulaOccurrence])

  def apply( proof: LKProof, omega: (Multiset[SchemaFormula], Multiset[SchemaFormula]) ): Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = apply(proof, getOmegaFOccFromEndSeq(proof, omega))

  var cut_anc_formulas: Set[FormulaOccurrence] = Set[FormulaOccurrence]()
  var i: Int = 0


  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = {
    implicit val c_ancs = cut_ancs
    implicit val factory = defaultFormulaOccurrenceFactory
    println("\nRule = "+proof.rule)

    proof match {
       case Axiom(s) => {
       // println("\nAxiom\n")
        // TODO: this is also used in the skolemization algorithm. refactor into Axiom.copy( proof )?
      val ant = s.antecedent
      val succ = s.succedent
      val ax = Axiom( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
      var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ax.root.antecedent( p._2 ) ))
      new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> ax.root.succedent( p._2 )))

      new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] + Pair(ax, new_map)
      }

      case SchemaProofLinkRule(root, link, indices) => {
        //println("subSeqOmegaBar = "+printSchemaProof.sequentToString(subSeqOmegaBar))
        val fresh_param: IntVar = IntVar(new VariableStringSymbol("n"))
   //     println(link+" , "+indices.head)
        //TODO : check name, name of the proof
        val ant = root.antecedent.filter(f => !cut_ancs.contains(f))
        val succ = root.succedent.filter(f => !cut_ancs.contains(f))
        val l:HashMultiset[SchemaFormula] = root.antecedent.map(fo => fo.formula).filter(f => cut_ancs.map(fo => fo.formula).contains(f)).foldLeft(HashMultiset[SchemaFormula])((hs,f) => hs + f.asInstanceOf[SchemaFormula])
        val r:HashMultiset[SchemaFormula] = root.succedent.map(fo => fo.formula).filter(f => cut_ancs.map(fo => fo.formula).contains(f)).foldLeft(HashMultiset[SchemaFormula])((hs,f) => hs + f.asInstanceOf[SchemaFormula])
        val cl_n = IndexedPredicate( new ClauseSetSymbol(link, (l,r) ), fresh_param::Nil )
    //    println("new_seq = "+printSchemaProof.sequentToString(new_seq))
        val pair = Pair(ant.map(fo => fo.formula) ++: (cl_n +: Seq.empty[SchemaFormula]), succ.map(fo => fo.formula))
        pair._1.foreach(f => println(printSchemaProof.formulaToString(f)))
        println("|-")
        pair._2.foreach(f => println(printSchemaProof.formulaToString(f)))
//        println("ant.size = "+pair._1.foreach(f => )+"\n"+"succ.size = "+succ.size)
        val ax = SchemaProofLinkRule(pair, link, indices)

        println("cut_anc = " + cut_ancs.size)
        cut_ancs.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
        var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ax.root.antecedent( p._2 ) ))
        new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> ax.root.succedent( p._2 )))
        println("new_map = " + new_map.size)
        new_map.foreach(p => println(printSchemaProof.formulaToString(p._1.formula) + " -> "+printSchemaProof.formulaToString(new_map(p._1).formula)))
        new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] + Pair(ax, new_map)
      }

      case AndLeftEquivalenceRule1(p, s, a, m) => {
       // println("\nAndLeftEquivalenceRule1\n")
        handleEquivalenceSchemaRule(proof, p, a, m, AndEquivalenceRule1.apply)
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
       // println("\nAndRightEquivalenceRule1\n")
        handleEquivalenceSchemaRule(proof, p, a, m, AndEquivalenceRule1.apply)
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
       // println("\nOrRightEquivalenceRule1\n")
        handleEquivalenceSchemaRule(proof, p, a, m, OrEquivalenceRule1.apply)
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
       // println("\nAndLeftEquivalenceRule3\n")
        handleEquivalenceSchemaRule(proof, p, a, m, AndEquivalenceRule3.apply)
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        //println("\nOrRightEquivalenceRule3\n")
        handleEquivalenceSchemaRule(proof, p, a, m, OrEquivalenceRule3.apply)
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
      case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply )
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

      case _ => throw new Exception("No such a rule in Projections.apply")
    }
  }


  def handleEquivalenceSchemaRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, constructor: (LKProof, FormulaOccurrence, SchemaFormula) => LKProof)(implicit cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
  {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    println("\nRule = "+proof.rule)

    if (cut_ancs.contains( m ) )
      handleUnaryCutAnc( proof, s )
    else
      s.map( pm => {
     //   println("\nauxf = "+printSchemaProof.formulaToString(pm._2( a ).formula))
        //printSchemaProof(pm._1)
        val new_p = constructor( pm._1, pm._2( a ), m.formula.asInstanceOf[SchemaFormula] )
        (new_p, copyMapToDescendant( proof, new_p, pm._2) )
    } )
  }

  def handleBinaryESAnc( proof: LKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof,
    s1: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    s2: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) =
  {
   //   println("\n\n     handleBinaryESAnc : \n")

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
    Pair( proof.root.antecedent.filter( fo => !cut_ancs.contains( fo ) ),
          proof.root.succedent.filter( fo => !cut_ancs.contains( fo ) ) )

  // Handles the case of a binary rule operating on a cut-ancestor.
  def handleBinaryCutAnc( proof: LKProof, p1: LKProof, p2: LKProof,
    s1: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    s2: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = {

  //  println("\n\n     handleBinaryCutAnc : \n")

   // println("p2: ")
   // println(printSchemaProof.sequentToString(p2.root))
  //  println("p1: ")
  //  println(printSchemaProof.sequentToString(p1.root))


  //  println("getESAncs( p2, cut_ancs ) ")
 //   getESAncs( p2, cut_ancs )._1.foreach( fo => println(fo.formula.toStringSimple))
 //   getESAncs( p2, cut_ancs )._2.foreach( fo => println(fo.formula.toStringSimple))
    //println("getESAncs( p1, cut_ancs ) ")
    //getESAncs( p1, cut_ancs )._1.foreach( fo => println(fo.formula.toStringSimple))
    //getESAncs( p1, cut_ancs )._2.foreach( fo => println(fo.formula.toStringSimple))

    val new_p1 = weakenESAncs( getESAncs( p2, cut_ancs ), s1 )
    val new_p2 = weakenESAncs( getESAncs( p1, cut_ancs ), s2 )

    copyMapsToDescLeft( proof, new_p1 ) ++
    copyMapsToDescLeft( proof, new_p2 )
    }

  // Apply weakenings to add the end-sequent ancestor of the other side
  // to the projection. Update the relevant maps.
  def weakenESAncs( esancs: Pair[Seq[FormulaOccurrence], Seq[FormulaOccurrence]],
    s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] ) = {
    //    println("\n\n\n    weakenESAncs : \n")

  //  println("esancs left: ")
 //   esancs._1.foreach( x => println(x.formula.toStringSimple))
 //   println("esancs right: ")
 //   esancs._2.foreach( x => println(x.formula.toStringSimple))

    val wl = s.map( p =>
      esancs._1.foldLeft( p )( (p, fo) => {
      val w = WeakeningLeftRule( p._1, fo.formula )
      val m = copyMapsToDescRight( w, p._2 ) + ( fo -> w.prin.head )
   //   println("new end-sequent after weakleft: " + printSchemaProof.sequentToString(w.root))
      (w, m)
    } ) )
    wl.map( p =>
      esancs._2.foldLeft( p )( (p, fo) => {
      val w = WeakeningRightRule( p._1, fo.formula )
      val m = copyMapsToDescRight( w, p._2 ) + ( fo -> w.prin.head )
      //assert( m(fo) == w.prin.head )
   //   println("new end-sequent after weakright: " + printSchemaProof.sequentToString(w.root))
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
      println("handleContractionRule")
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
    println("handleUnaryRule")
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
      println("handleWeakeningRule, s.size = "+s.size)
      cut_ancs.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
      if (cut_ancs.contains( m ) )
        handleUnaryCutAnc( proof, s )
      else
        s.map( pm => {
          val new_p = constructor( pm._1, m.formula )
             val new_map = copyMapToDescendant( proof, new_p, pm._2) + ( m -> new_p.prin.head )
             println("new_map = " + new_map.size)
             new_map.foreach(p => println(printSchemaProof.formulaToString(p._1.formula) + " -> "+printSchemaProof.formulaToString(new_map(p._1).formula)))
//          (new_p, copyMapToDescendant( proof, new_p, pm._2) + ( m -> new_p.prin.head ) )
          (new_p, new_map )
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
    println("handleNegRule")
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
    println("handleBinaryRule")

   println("\nPrinting cut_anc and m in "+proof.rule+" : ")
    cut_ancs.foreach(fo => println(printSchemaProof.formulaToString(fo.formula)))
    print("\nm = "+m.formula)
   // printSchemaProof.formulaToString(m.formula)

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
      println("old_p.getDescendantInLowerSequent( p._1 ) "+printSchemaProof.formulaToString(p._1.formula))
       println("desc.get "+printSchemaProof.formulaToString(desc.get.formula))
       println("old_proof : " + printSchemaProof.sequentToString(old_p.root))
      println("new_p : " + printSchemaProof.sequentToString(new_p.root))
      println("p_2 = "+printSchemaProof.formulaToString(p._2.formula))
        if (desc != None)
          m + (desc.get -> new_p.getDescendantInLowerSequent( p._2 ).get )
        else
          m
      } )


  // Cvetan
  // gets all FOccs from proof which correspond to the cc omega
  def getOmegaFOccFromEndSeq (p: LKProof, omega: (Multiset[SchemaFormula], Multiset[SchemaFormula])): Set[FormulaOccurrence] = {
        val seq = p.root
        val s = Set[FormulaOccurrence]()
        s

     //uncomment!   seq.antecedent.filter(oc => omega._1.contains(oc.formula)) ++ seq.succedent.filter(oc => omega._2.contains(oc.formula))
  }
  /*
    // adds to the cut-ancestors of p all ancestors of formula occurrences in a given omega
    object getCutAncestorsOmega {
      def apply(p: LKProof, omega: (Multiset[SchemaFormula], Multiset[SchemaFormula])) = apply(p, getOmegaFOccFromEndSeq(p.root, omega))

      def apply( p: LKProof, ancOfOmegaSeq: Set[FormulaOccurrence] ) : Set[FormulaOccurrence] = p match {
          case CutRule(p1, p2, _, a1, a2) => getCutAncestorsOmega( p1, getAncOfSetOfFOccs(ancOfOmegaSeq) ) ++ getCutAncestorsOmega( p2, getAncOfSetOfFOccs(ancOfOmegaSeq) ) ++
                                             Axiom.toSet( getAncestors( a1 ) ) ++ Axiom.toSet( getAncestors( a2 ) )

          case UnaryLKProof(_,p,_,_,_) => getCutAncestors( p, getAncOfSetOfFOccs(ancOfOmegaSeq) )
          case BinaryLKProof(_, p1, p2, _, _, _, _) => getCutAncestorsOmega( p1, getAncOfSetOfFOccs(ancOfOmegaSeq) ) ++ getCutAncestorsOmega( p2, getAncOfSetOfFOccs(ancOfOmegaSeq) )
          case Axiom(_) => Set[FormulaOccurrence]() ++ getAncOfSetOfFOccs(ancOfOmegaSeq)
          // support LKsk
          case UnaryLKskProof(_,p,_,_,_) => getCutAncestorsOmega( p, getAncOfSetOfFOccs(ancOfOmegaSeq) )
          // support SLK
          case UnarySchemaProof(_,p,_,_,_) => getCutAncestorsOmega( p, getAncOfSetOfFOccs(ancOfOmegaSeq) )
          case SchemaProofLinkRule(_, _, _) => Set[FormulaOccurrence]() ++ getAncOfSetOfFOccs(ancOfOmegaSeq)
      }
    }


    // gets all ancestors of FOccs from a given set of FOccs
    def getAncOfSetOfFOccs (fos: Set[FormulaOccurrence] ) : Set[FormulaOccurrence] = {
        fos.foldLeft(Set[FormulaOccurrence]())((x,y) => x ++ (y.getAncestors + y) )
    }
    */
    def removeAllCutAnc(s: Sequent, cut_ancs: Set[FormulaOccurrence]): Sequent = s

}


//TODO: refactor, taken from substitution
object printSchemaProof {
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.{Or => HOLOr, Neg => HOLNeg, And => HOLAnd, _}
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.schema.{IntVar, IntZero, IndexedPredicate, SchemaFormula, Succ, BigAnd, BigOr, IntegerTerm, IntConst}
import at.logic.calculi.slk._


   def formulaToString(f:LambdaExpression) : String = f match {
     case BigAnd(v, formula, init, end) =>
 	        "⋀" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

     case BigOr(v, formula, init, end) =>
 	        "⋁" + formulaToString(v) + "=(" + formulaToString(init) + ".." + formulaToString(end) + ")(" + formulaToString(formula) + ")"

     case t : IntegerTerm  => parseIntegerTerm(t, 0)
     case App(x,y) => x match {
       case App(Var(name,tp),z) =>
         if (name.toString.matches("""[\w\p{InGreek}]*""")) name.toString+"("+formulaToString(z)+","+formulaToString(y)+")"
         else "("+formulaToString(z)+" "+name.toString()+" "+formulaToString(y)+")"
       case Var(name,tp) => tp match {
         case ->(To(), To()) => name.toString+formulaToString(y)
         case _ => y match {
           case Abs(x1,y1) => "("+name.toString+formulaToString(x1)+")"+formulaToString(y1)
           case _ => name.toString()+"("+formulaToString(y)+")"
        }
       }
       case _ => formulaToString(x) +"("+ formulaToString(y) +")"
     }
    case Var(name,t) => name.toString()
    case Abs(x,y) => formulaToString(y)
    case  x : Any    => "(unmatched class: "+x.getClass() + ")"
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int) : String = t match {
 	    // FIXME: in the first case, we implicitely assume
 	    // that all IntConsts are 0!
 	    // this is just done for convenience, and should be changed ASAP
 	    case z : IntConst => n.toString
 	    case IntZero() => n.toString

 	    case v : IntVar => if (n > 0)
 	        v.toStringSimple + "+" + n.toString
 	      else
 	        v.toStringSimple
 	    case Succ(t) => parseIntegerTerm( t, n + 1 )
  }

  def sequentToString(s : Sequent) : String = {
    var sb = new scala.StringBuilder()
    var first = true
    for (f <- s.antecedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.append(" \u22a2 ")
    first =true
    for (f <- s.succedent) {
      if (! first) sb.append(", ")
      else first = false
      sb.append(formulaToString(f.formula))
    }
    sb.toString
  }
  //def sequentToString(seq : Sequent): String = {
  //  seq.antecedent.toList.map(fo => fo.formula.toString+" <> " )+" |- "+ seq.succedent.toList.map(fo => fo.formula.toString+" <> ")
  //}

  def apply(p: LKProof):Unit = p match {
    case SchemaProofLinkRule( seq, _, _) => println("\n SchemaProofLinkRule : "+sequentToString(seq))
    case Axiom(seq) => println("\n Axiom : " + sequentToString(seq))

    case UnaryLKProof(_, up, r, _, _) => {
      apply(up)
      println("\n UnaryProof : " + sequentToString(r))
    }
    case BinaryLKProof(_, up1, up2, r, _, _, _) => {
      apply(up1)
      apply(up2)
      println("\n BinaryProof : " + sequentToString(r))
    }



    case AndEquivalenceRule1(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case AndEquivalenceRule2(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case AndEquivalenceRule3(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case OrEquivalenceRule1(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case OrEquivalenceRule2(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case OrEquivalenceRule3(up, r, _, _) =>  {
      apply(up)
      println("\n UnaryProof : "+sequentToString(r))
    }
    case _ => println("ERROR in printSchemaProof")
  }
}

object DeleteTautology {
    def apply(l : List[Sequent]): List[Sequent] = {
        l.filter( seq => {
             seq.antecedent.toList.map(fo => fo.formula).intersect( seq.succedent.toList.map(fo => fo.formula) ) == List[Sequent]()
        } ).map(seq1 => DeleteReduntantFOfromSequent(seq1))
    }
}
import at.logic.calculi.lk.base.types.FSequent
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
                    )
                    true
                else
                    member(seq, ls)
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

