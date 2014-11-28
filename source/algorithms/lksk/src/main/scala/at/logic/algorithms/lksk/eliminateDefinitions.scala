package at.logic.algorithms.lksk

import at.logic.language.hol._
import at.logic.calculi.lk.{Axiom => _, WeakeningLeftRule => _, WeakeningRightRule => _, _}
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk._

import scala.collection.mutable

object eliminateDefinitions {
  def toLabelledSequent( so: Sequent )
    = new LabelledSequent( so.antecedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ),
                           so.succedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ) )


  def apply( p: LKProof ) = rec( p )._1

  def rec( proof: LKProof ) : (LKProof, mutable.Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence])  =
  {
    proof match
    {
      case r @ CutRule( p1, p2, _, a1, a2 ) => {
        // first left, then right
        val rec1 = rec( p1 )
        val rec2 = rec( p2 )
        val new_proof = CutRule( rec1._1, rec2._1, rec1._2( a1.asInstanceOf[LabelledFormulaOccurrence] ), rec2._2( a2.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls1 = toLabelledSequent(p1.root)
        val ls2 = toLabelledSequent(p2.root)
        return (new_proof,
                     computeMap( ls1.l_antecedent ++ ls1.l_succedent.filter(_ != a1), r, new_proof, rec1._2 ) ++
                     computeMap( ls2.l_antecedent.filter(_ != a2) ++ ls2.l_succedent, r, new_proof, rec2._2 ))
      }
      case r @ AndRightRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], AndRightRule.apply )
      }
      case r @ OrLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], OrLeftRule.apply )
      }
      case r @ ImpLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], ImpLeftRule.apply )
      }
      case r @ EquationLeft1Rule( p1, p2, _, a1, a2, _, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], m.formula, EquationLeftRule.apply )
      }
      case r @ EquationLeft2Rule( p1, p2, _, a1, a2, _, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], m.formula, EquationLeftRule.apply )
      }
      case r @ EquationRight1Rule( p1, p2, _, a1, a2, _, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], m.formula, EquationRightRule.apply )
      }
      case r @ EquationRight2Rule( p1, p2, _, a1, a2, _, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], m.formula, EquationRightRule.apply )
      }
      case Axiom(so) => {
        val ls = toLabelledSequent(so)
        val ant_occs = ls.l_antecedent.toList
        val succ_occs = ls.l_succedent.toList
        val (a,labels) = Axiom.createDefault(new FSequent(ant_occs.map( fo => fo.formula ), succ_occs.map( fo => fo.formula ) ),
                                    Tuple2( ant_occs.map( fo => fo.skolem_label ).toList,
                                          succ_occs.map( fo => fo.skolem_label ).toList ) )
        val map = new mutable.HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
        val las = toLabelledSequent(a.root)
        las.l_antecedent.zip(ant_occs).foreach(p => {println(p); map.update( p._2, p._1)})
        las.l_succedent.zip(succ_occs).foreach(p => {println(p); map.update( p._2, p._1)})
        (a, map)
      }
      case WeakeningLeftRule(p, s, m) => {
        val new_parent = rec( p )
        handleWeakening( ( new_parent._1, new_parent._2 ), p, proof, (p, m, l) => WeakeningLeftRule.createDefault(p,m,l), m )
      }
      case WeakeningRightRule(p, s, m) => {
        val new_parent = rec( p )
        handleWeakening( ( new_parent._1, new_parent._2 ), p, proof, (p, m, l) => WeakeningRightRule.createDefault(p,m,l), m )
      }
      case ContractionLeftRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        handleContraction( ( new_parent._1, new_parent._2 ), p, proof, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], ContractionLeftRule.apply )
      }
      case ContractionRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        handleContraction( ( new_parent._1, new_parent._2 ), p, proof, a1.asInstanceOf[LabelledFormulaOccurrence], a2.asInstanceOf[LabelledFormulaOccurrence], ContractionRightRule.apply )
      }
      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = rec( p )
        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), f )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = rec( p )
        val new_proof = AndLeft2Rule( new_parent._1, f, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = rec( p )
        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), f )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = rec( p )
        val new_proof = OrRight2Rule( new_parent._1, f, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        val new_proof = ImpRightRule( new_parent._1,
                                      new_parent._2( a1.asInstanceOf[LabelledFormulaOccurrence] ),
                                      new_parent._2( a2.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }

      case NegLeftRule(p, s, a, m) => {
        val new_parent = rec( p )
        val new_proof = NegLeftRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = rec( p )
        val new_proof = NegRightRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ) )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case r @ DefinitionRightRule( p, s, a, m ) => {
        handleDefinition(r,p)
      }
      case r @ DefinitionLeftRule( p, s, a, m ) => {
        handleDefinition(r,p)
      }
      case ForallLeftRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        val new_proof = ForallLeftRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), m.formula, t )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsRightRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        val new_proof = ExistsRightRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), m.formula, t )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsLeftRule( p, s, a, m, v ) => {
        val new_parent = rec( p )
        val new_proof = ExistsLeftRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), m.formula, v )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallRightRule( p, s, a, m, v ) => {
        val new_parent = rec( p )
        val new_proof = ForallRightRule( new_parent._1, new_parent._2( a.asInstanceOf[LabelledFormulaOccurrence] ), m.formula, v )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallSkRightRule( p, s, a, m, sub ) => {
        val new_parent = rec( p )
        val new_proof = ForallSkRightRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], m.formula, sub )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkLeftRule( p, s, a, m, sub ) => {
        val new_parent = rec( p )
        val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], m.formula, sub )
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallSkLeftRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], m.formula, t, false )  // ToDo: I have no idea whether the last parameter should be true or false
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkRightRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], m.formula, t, false ) // ToDo: I have no idea whether the last parameter should be true or false
        val ls = toLabelledSequent(p.root)
        ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, proof, new_proof, new_parent._2 ) )
      }
    }
  }

  def handleDefinition(r:LKProof,  p:LKProof) = {
    val new_parent = rec( p )
    val newProof = new_parent._1
    val premiseMap = new_parent._2
    //println("premiseMap: ")
    //premiseMap.map(kv => {println(kv._1 + "  --->  " + kv._2)})
    //println("newProof: " + newProof)
    val map = new mutable.HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
    val ls = toLabelledSequent(r.root)

    ls.l_antecedent.foreach( fo => {println(fo); println(fo.parents.head); map.update( fo , premiseMap(fo.parents.head) )} )
    ls.l_succedent.foreach( fo => map.update( fo , premiseMap(fo.parents.head) ) )
    println("map")
    map.foreach( pair => println(pair) )
    (newProof, map)
  }

  def handleWeakening( new_parent: (LKProof, mutable.Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]),
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula, TypeSynonyms.Label) => LKProof with PrincipalFormulas,
                       m: LabelledFormulaOccurrence ) = {
    val new_proof = constructor( new_parent._1, m.formula, m.skolem_label )
    val ls = toLabelledSequent(old_parent.root)
    ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, old_proof, new_proof, new_parent._2 ) + Tuple2(m, new_proof.prin.head.asInstanceOf[LabelledFormulaOccurrence] ) )
  }

  def handleContraction( new_parent: (LKProof, mutable.Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]),
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: LabelledFormulaOccurrence,
                         a2: LabelledFormulaOccurrence,
                         constructor: (LKProof, LabelledFormulaOccurrence, LabelledFormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
    val ls = toLabelledSequent(old_parent.root)
    ( new_proof, computeMap( ls.l_antecedent ++ ls.l_succedent, old_proof, new_proof, new_parent._2 ) )
  }

  def handleEquational( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: LabelledFormulaOccurrence, a2: LabelledFormulaOccurrence, m :HOLFormula,
    constructor: (LKProof, LKProof, LabelledFormulaOccurrence, LabelledFormulaOccurrence, HOLFormula) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1 )
      val rec2 = rec( p2 )
      val ls1 = toLabelledSequent(p1.root)
      val ls2 = toLabelledSequent(p2.root)
      val new_proof = constructor( rec1._1, rec2._1, rec1._2( a1 ), rec2._2( a2 ) , m )
      ( new_proof, computeMap( ls1.l_antecedent ++ ls1.l_succedent, r, new_proof, rec1._2 ) ++
                   computeMap( ls2.l_antecedent ++ ls2.l_succedent, r, new_proof, rec2._2 ) )
  }

  def handleBinaryProp( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: LabelledFormulaOccurrence, a2: LabelledFormulaOccurrence,
    constructor: (LKProof, LKProof, LabelledFormulaOccurrence, LabelledFormulaOccurrence) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1 )
      val rec2 = rec( p2 )
      val ls1 = toLabelledSequent(p1.root)
      val ls2 = toLabelledSequent(p2.root)
      val new_proof = constructor( rec1._1, rec2._1, rec1._2( a1 ), rec2._2( a2 ) )
      ( new_proof, computeMap( ls1.l_antecedent ++ ls1.l_succedent, r, new_proof, rec1._2 ) ++
                   computeMap( ls2.l_antecedent ++ ls2.l_succedent, r, new_proof, rec2._2 ) )
  }

  def computeMap( occs: Seq[LabelledFormulaOccurrence], old_proof: LKProof,
                  new_proof: LKProof, old_map : mutable.Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  {
    val map = new mutable.HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get.asInstanceOf[LabelledFormulaOccurrence],
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get.asInstanceOf[LabelledFormulaOccurrence] ) )
    map
  }

}
