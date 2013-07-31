package at.logic.algorithms.lk

import at.logic.calculi.lksk.{ForallSkLeftRule, ExistsSkRightRule, ExistsSkLeftRule, ForallSkRightRule}
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.propositionalRules._
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.immutable.HashSet

import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}

import at.logic.calculi.lksk.lkskExtractors.{UnaryLKskProof}

import at.logic.calculi.slk._

import at.logic.language.hol._
import at.logic.language.lambda.substitutions
import substitutions.Substitution
import scala.collection.mutable

object ProofTransformationUtils {
  // FIXME: adapted from LKtoLKskc!
  def computeMap[T<:FormulaOccurrence]( occs: Seq[T], old_proof: LKProof,
                  new_proof: LKProof, old_map : Map[T, T]) :
  Map[T, T] = {
    //compute a mapping in which each formula occurrence fo in occs in old_proof is mapped to the descendant in the new proof
    occs.foldLeft(Map[T, T]())( (map, fo) => { map +
      ((old_proof.getDescendantInLowerSequent( fo ).get, new_proof.getDescendantInLowerSequent( old_map(fo) ).get ).asInstanceOf[(T,T)]  ) })
  }

}

object getCutAncestors {
  def apply( p: LKProof ): Set[FormulaOccurrence] = {
    p match {
      case TermEquivalenceRule1(p1, _, _, _) => return getCutAncestors( p1 )
      //      case TermLeftEquivalenceRule1(p1, _, _, _) => getCutAncestors( p1 )
      //      case TermRightEquivalenceRule1(p1, _, _, _) => getCutAncestors( p1 )
      case CutRule(p1, p2, _, a1, a2) => getCutAncestors( p1 ) ++ getCutAncestors( p2 ) ++
        getAncestors( a1 ) ++ getAncestors( a2 )
      case UnaryLKProof(_,p1,_,_,_) => getCutAncestors( p1 )
      case BinaryLKProof(_, p1, p2, _, _, _, _) => getCutAncestors( p1 ) ++ getCutAncestors( p2 )
      case Axiom(_) => Set[FormulaOccurrence]()
      // support LKsk
      case UnaryLKskProof(_,p1,_,_,_) => getCutAncestors( p1 )
      // support SLK
      case UnarySchemaProof(_,p1,_,_,_) => getCutAncestors( p1 )
      case SchemaProofLinkRule(_, _, _) => Set[FormulaOccurrence]()
      case ForallHyperLeftRule(p1, r, a, p, _) => getCutAncestors( p1 )
      case ExistsHyperRightRule(p1, r, a, p, _) => getCutAncestors( p1 )
      case ForallHyperRightRule(p1, r, a, p, _) => getCutAncestors( p1 )
      case ExistsHyperLeftRule(p1, r, a, p, _) => getCutAncestors( p1 )
      case _ => throw  new Exception("\n\nMissing rule in getCutAncestors(...) : "+p.name+"\n\n")
    }
  }
  // This method returns only ancestors of cut-formulas that satisfy a given predicate.
  def apply( p: LKProof, predicate : HOLFormula => Boolean )
    : Set[FormulaOccurrence] = p match {
      case CutRule(p1, p2, _, a1, a2) => if (predicate(a1.formula)) {
          getCutAncestors( p1, predicate ) ++ getCutAncestors( p2, predicate ) ++ getAncestors( a1 ) ++ getAncestors( a2 )
        } else {
          getCutAncestors( p1, predicate ) ++ getCutAncestors( p2, predicate )
        }
      case UnaryLKProof(_,p,_,_,_) => getCutAncestors( p, predicate )
      case BinaryLKProof(_, p1, p2, _, _, _, _) => getCutAncestors( p1, predicate ) ++ getCutAncestors( p2, predicate )
      case Axiom(_) => Set[FormulaOccurrence]()
      // support LKsk
      case UnaryLKskProof(_,p,_,_,_) => getCutAncestors( p, predicate )
      // support SLK
      case UnarySchemaProof(_,p,_,_,_) => getCutAncestors( p, predicate )
      case SchemaProofLinkRule(_, _, _) => Set[FormulaOccurrence]()
      case _ => throw  new Exception("\n\nMissing rule in getCutAncestors(...) : "+p.name+"\n\n")
    }
}

object getAncestors {
  def apply( o: FormulaOccurrence ) : Set[FormulaOccurrence] =
    o.ancestors.flatMap( a => getAncestors( a ) ).toSet ++ Set( o )

  def apply( o: Set[FormulaOccurrence] ) : Set[FormulaOccurrence] =
    o.foldLeft( new HashSet[FormulaOccurrence] )( (res, o) => res ++ apply( o ) )
}

object getAuxFormulas {
  def apply(proof: LKProof): Set[FormulaOccurrence] = proof match {
      case UnaryLKProof(_,p,_,auxs,main) => (getAuxFormulas( p ) ++ auxs.toSet) + main
      case BinaryLKProof(_,p1,p2,_,aux1,aux2,main) =>
        val set = getAuxFormulas( p1 ) ++ getAuxFormulas( p2 ) ++ Set(aux1,aux2)
        if (main == None) set
        else set + main.get
      case Axiom(_) => Set[FormulaOccurrence]()
      // support LKsk
      case UnaryLKskProof(_,p,_,auxs,main) => (getAuxFormulas( p ) ++ auxs.toSet) + main
      // support SLK
      case UnarySchemaProof(_,p,_,auxs,main) => (getAuxFormulas( p ) ++ auxs.toSet) + main
      case SchemaProofLinkRule(_, _, _) => Set[FormulaOccurrence]()
  }
}

object eliminateDefinitions {

  import at.logic.calculi.lk._
  import at.logic.calculi.lk.base._
  import ProofTransformationUtils.computeMap

  def apply( p: LKProof ) = rec( p )._1

  def rec( proof: LKProof ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence])  =
  {
    proof match
    {
      // FIXME: cast!?!
      case r @ CutRule( p1, p2, _, a1, a2 ) => {
        // first left, then right
        val rec1 = rec( p1 )
        val rec2 = rec( p2 )
        val new_proof = CutRule( rec1._1, rec2._1, rec1._2( a1 ), rec2._2( a2 ) )
        return (new_proof,
                     computeMap( p1.root.antecedent ++ p1.root.succedent.filter(_ != a1), r, new_proof, rec1._2 ) ++
                     computeMap( p2.root.antecedent.filter(_ != a2) ++ p2.root.succedent, r, new_proof, rec2._2 ))
      }
      case r @ AndRightRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, AndRightRule.apply )
      }
      case r @ OrLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, OrLeftRule.apply )
      }
      case r @ ImpLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, ImpLeftRule.apply )
      }
      case r @ EquationLeft1Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, EquationLeft1Rule.apply )
      }
      case r @ EquationLeft2Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, EquationLeft2Rule.apply )
      }
      case r @ EquationRight1Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, EquationRight1Rule.apply )
      }
      case r @ EquationRight2Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, EquationRight2Rule.apply )
      }
      case Axiom(so) => {
        val ant_occs = so.antecedent.toList
        val succ_occs = so.succedent.toList
        //println("ant_occs: " + ant_occs)
        //println("succ_occs: " + succ_occs)
        val a = Axiom(ant_occs.map( fo => fo.formula ), succ_occs.map( fo => fo.formula ))
        //println(" a : \n" + a)
        require(a.root.antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one")
        require(a.root.succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one")
        val map = Map[FormulaOccurrence, FormulaOccurrence]() ++
          (ant_occs zip a.root.antecedent) ++ (succ_occs zip a.root.succedent)

        //println(a.root)
        //println("Axiom map: " + map)

        (a, map)
      }
      case WeakeningLeftRule(p, s, m) => {
        val new_parent = rec( p )
        handleWeakening( ( new_parent._1, new_parent._2 ), p, proof, WeakeningLeftRule.apply, m )
      }
      case WeakeningRightRule(p, s, m) => {
        val new_parent = rec( p )
        handleWeakening( ( new_parent._1, new_parent._2 ), p, proof, WeakeningRightRule.apply, m )
      }
      case ContractionLeftRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        handleContraction( ( new_parent._1, new_parent._2 ), p, proof, a1, a2, ContractionLeftRule.apply )
      }
      case ContractionRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        handleContraction( ( new_parent._1, new_parent._2 ), p, proof, a1, a2, ContractionRightRule.apply )
      }
      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = rec( p )
        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), f )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = rec( p )
        val new_proof = AndLeft2Rule( new_parent._1, f, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = rec( p )
        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), f )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = rec( p )
        val new_proof = OrRight2Rule( new_parent._1, f, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p )
        val new_proof = ImpRightRule( new_parent._1,
                                      new_parent._2( a1 ),
                                      new_parent._2( a2 ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }

      case NegLeftRule(p, s, a, m) => {
        val new_parent = rec( p )
        val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = rec( p )
        val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case r @ DefinitionRightRule( p, s, a, m ) => {
        handleDefinition(r,p)
      }
      case r @ DefinitionLeftRule( p, s, a, m ) => {
        handleDefinition(r,p)
      }
      case ForallLeftRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        val new_proof = ForallLeftRule( new_parent._1, new_parent._2( a ), m.formula, t )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsRightRule( p, s, a, m, t ) => {
        val new_parent = rec( p )
        //println("exists_right")
        val new_proof = ExistsRightRule( new_parent._1, new_parent._2( a ), m.formula, t )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsLeftRule( p, s, a, m, v ) => {
        val new_parent = rec( p )
        val new_proof = ExistsLeftRule( new_parent._1, new_parent._2( a ), m.formula, v )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallRightRule( p, s, a, m, v ) => {
        val new_parent = rec( p )
        //println("forall")
        //println("new_parent: " + new_parent)
        //println(new_parent._2)
        val new_proof = ForallRightRule( new_parent._1, new_parent._2( a ), m.formula, v )
        //println("forall ok!")
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
    }
  }

  def handleDefinition(r:LKProof,  p:LKProof) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence])= {
    val new_parent = rec( p )
    val newProof = new_parent._1
    val premiseMap = new_parent._2
    //println("premiseMap: ")
    premiseMap.map(kv => {println(kv._1 + "  --->  " + kv._2)})
    //println("newProof: " + newProof)
    val emptymap = Map[FormulaOccurrence, FormulaOccurrence]()
    val antonlymap =  r.root.antecedent.foldLeft(emptymap)((m, fo) => m + ((fo , premiseMap(fo.ancestors.head))))
    val fullmap = r.root.succedent.foldLeft(antonlymap)((m, fo) => m + ((fo , premiseMap(fo.ancestors.head))))

    //println("map")
    fullmap.foreach( pair => println(pair) )
    (newProof, fullmap)
  }

  def handleWeakening( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
    val new_proof = constructor( new_parent._1, m.formula )
    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
  }

  def handleContraction( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }

  def handleEquational( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m :HOLFormula,
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1 )
      val rec2 = rec( p2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._2( a1 ), rec2._2( a2 ) , m )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._2 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._2 ) )
  }

  def handleBinaryProp( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence,
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1 )
      val rec2 = rec( p2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._2( a1 ), rec2._2( a2 ) )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._2 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._2 ) )
  }

}

object regularize {
  import ProofTransformationUtils.computeMap

  def apply( p: LKProof ) = {
    val blacklist = findVariableNames(p)
    //println("regularization blacklist is: "+blacklist)
    rec( p, blacklist )
  }

  def rec( proof: LKProof, vars: Set[String] ) : (LKProof, Set[String], Map[FormulaOccurrence, FormulaOccurrence] ) =
  {
    //implicit val factory = PointerFOFactoryInstance
    proof match
    {
      case r @ CutRule( p1, p2, _, a1, a2 ) => {
        // first left, then right
        val rec1 = rec( p1, vars )
        val rec2 = rec( p2, vars ++ rec1._2 )
        val new_proof = CutRule( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) )
        ( new_proof, rec2._2, computeMap( p1.root.antecedent ++
        (p1.root.succedent.filter(_ != a1)), r, new_proof, rec1._3 ) ++
                     computeMap( (p2.root.antecedent.filter(_ != a2)) ++ p2.root.succedent, r, new_proof, rec2._3 ) )
      }
      case r @ AndRightRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, AndRightRule.apply )
      }
      case r @ OrLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, OrLeftRule.apply )
      }
      case r @ ImpLeftRule( p1, p2, _, a1, a2, _ ) => {
        handleBinaryProp( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, vars, ImpLeftRule.apply )
      }
      case r @ EquationLeft1Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationLeft1Rule.apply )
      }
      case r @ EquationLeft2Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationLeft2Rule.apply )
      }
      case r @ EquationRight1Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationRight1Rule.apply )
      }
      case r @ EquationRight2Rule( p1, p2, _, a1, a2, m ) => {
        handleEquational( r.asInstanceOf[BinaryLKProof with AuxiliaryFormulas], p1, p2, a1, a2, m.formula, vars, EquationRight2Rule.apply )
      }
      case Axiom(so) => {
        val ant_occs = so.antecedent
        val succ_occs = so.succedent
        val a = Axiom(ant_occs.map( fo => fo.formula ), succ_occs.map( fo => fo.formula ))
        //val map = Map[FormulaOccurrence, FormulaOccurrence]()
        //a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
        //a.root.antecedent.zip(ant_occs).foreach(p => map.update( p._2, p._1))
        //a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
        //a.root.succedent.zip(succ_occs).foreach(p => map.update( p._2, p._1))

        require(a.root.antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one")
        require(a.root.succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one")
        val map = Map[FormulaOccurrence, FormulaOccurrence]() ++
          (ant_occs zip a.root.antecedent) ++ (succ_occs zip a.root.succedent)


        (a, vars, map)
      }
      case WeakeningLeftRule(p, s, m) => {
        val new_parent = rec( p, vars )
        handleWeakening( ( new_parent._1, new_parent._3 ), p, proof, new_parent._2, WeakeningLeftRule.apply, m )
      }
      case WeakeningRightRule(p, s, m) => {
        val new_parent = rec( p, vars )
        handleWeakening( ( new_parent._1, new_parent._3 ), p, proof, new_parent._2, WeakeningRightRule.apply, m )
      }
      case ContractionLeftRule(p, s, a1, a2, m) => {
        val new_parent = rec( p, vars )
        handleContraction( ( new_parent._1, new_parent._3 ), p, proof, a1, a2, new_parent._2, ContractionLeftRule.apply )
      }
      case ContractionRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p, vars )
        handleContraction( ( new_parent._1, new_parent._3 ), p, proof, a1, a2, new_parent._2, ContractionRightRule.apply )
      }
      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = rec( p, vars )
        val new_proof = AndLeft1Rule( new_parent._1, new_parent._3( a ), f )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = rec( p, vars )
        val new_proof = AndLeft2Rule( new_parent._1, f, new_parent._3( a ) )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = rec( p, vars )
        val new_proof = OrRight1Rule( new_parent._1, new_parent._3( a ), f )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = rec( p, vars )
        val new_proof = OrRight2Rule( new_parent._1, f, new_parent._3( a ) )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = rec( p, vars )
        val new_proof = ImpRightRule( new_parent._1,
                                      new_parent._3( a1 ),
                                      new_parent._3( a2 ) )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }

      case NegLeftRule(p, s, a, m) => {
        val new_parent = rec( p, vars )
        val new_proof = NegLeftRule( new_parent._1, new_parent._3( a ) )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = rec( p, vars )
        val new_proof = NegRightRule( new_parent._1, new_parent._3( a ) )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case DefinitionRightRule( p, s, a, m ) => {
        val new_parent = rec( p, vars )
        val new_proof = DefinitionRightRule( new_parent._1, new_parent._3( a ), m.formula )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case DefinitionLeftRule( p, s, a, m ) => {
        val new_parent = rec( p, vars )
        val new_proof = DefinitionLeftRule( new_parent._1, new_parent._3( a ), m.formula )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case ForallLeftRule( p, s, a, m, t ) => {
        val new_parent = rec( p, vars )
        val new_proof = ForallLeftRule( new_parent._1, new_parent._3( a ), m.formula, t )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case ExistsRightRule( p, s, a, m, t ) => {
        val new_parent = rec( p, vars )
        val new_proof = ExistsRightRule( new_parent._1, new_parent._3( a ), m.formula, t )
        ( new_proof, new_parent._2, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._3 ) )
      }
      case ExistsLeftRule( p, s, a, m, v ) => {
        val vname = v.name.toString
        val (nparent, blacklist, table) = rec( p, vars + vname )
        val (new_proof, new_blacklist, new_map) = if ( blacklist.contains( vname ) ) // rename eigenvariable
        {
          // FIXME: casts!?
          val new_var_name = (x:Int) => v.name.toString.replaceAll("_.*$","")+"_{"+x+"}" // {} are obligatory for prooftool
          val new_var = freshVar.get( v.exptype, blacklist, new_var_name, v.factory ).asInstanceOf[HOLVar]
          val new_new_parent = applySubstitution( nparent, Substitution[HOLExpression]( v, new_var ) )
          val new_map =  table.transform( (k, v) => new_new_parent._2( v ) ) // compose maps
            ( ExistsLeftRule( new_new_parent._1, new_map( a ), m.formula, new_var ), blacklist + new_var.name.toString, new_map )
        } else {
            ( ExistsLeftRule( nparent, table( a ), m.formula, v ), blacklist + v.name.toString, table )
        }

        ( new_proof, new_blacklist, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_map ) )
      }
      case ForallRightRule( p, s, a, m, v ) => {
        val vname = v.name.toString
        val (nparent, blacklist, table) = rec( p, vars + vname )
        val (new_proof, new_blacklist, new_map) = if ( blacklist.contains( vname ) ) // rename eigenvariable
        {
          // FIXME: casts!?
          val new_var_name = (x:Int) => v.name.toString.replaceAll("_.*$","")+"_{"+x+"}" // {} are obligatory for prooftool
          val new_var = freshVar.get( v.exptype, blacklist, new_var_name, v.factory ).asInstanceOf[HOLVar]
          val new_new_parent = applySubstitution( nparent, Substitution[HOLExpression]( v, new_var ) )
          val new_map = table.transform( (k, v) => new_new_parent._2( v ) ) // compose maps
          ( ForallRightRule( new_new_parent._1, new_map( a ), m.formula, new_var ), blacklist + new_var.name.toString, new_map )
        } else
          ( ForallRightRule( nparent, table( a ), m.formula, v ), blacklist + v.name.toString, table )
        ( new_proof, new_blacklist, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_map ) )
      }
    }
  }

  def handleWeakening( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                       old_parent: LKProof,
                       old_proof: LKProof,
                       vars: Set[String],
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
    val new_proof = constructor( new_parent._1, m.formula )
    ( new_proof, vars, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )  
  }

  def handleContraction( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         vars: Set[String],
                         constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
    ( new_proof, vars, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }

  def handleEquational( r: BinaryLKProof with AuxiliaryFormulas,
                        p1: LKProof, p2: LKProof,
                        a1: FormulaOccurrence, a2: FormulaOccurrence,
                        m :HOLFormula, vars: Set[String],
                        constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) , m )
      ( new_proof, rec2._2, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }

  def handleBinaryProp( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, vars: Set[String],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) )
      ( new_proof, rec2._2, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }


  def findVariableNames(e:LambdaExpression) : Set[String] = e match {
    case Var(sym,_) => Set(sym.toString)
    case App(s,t) => findVariableNames(s) ++ findVariableNames(t)
    case Abs(v,t) => Set(v.name.toString) ++ findVariableNames(t)
  }

  def findVariableNames(root : Sequent) : Set[String] = (root.antecedent ++ root.succedent).foldLeft (Set[String]()) ((x:Set[String], y:FormulaOccurrence) => x ++ findVariableNames(y.formula))
  def findVariableNames(p : LKProof) : Set[String] = p.fold (findVariableNames)  (_ ++ findVariableNames(_)) (_ ++ _ ++ findVariableNames(_))

}

object replaceSubproof {
  // This function works on object equality of two proofs, checking that "proof" contains "subproof" in object level.
  def apply(proof: LKProof, subproof: LKProof, newSubproof: LKProof) : LKProof = {
    if (! proof.contains(subproof)) throw new Exception("There is no such subproof to replace")
    else if (subproof == newSubproof) proof
    else replace(proof, subproof, newSubproof)
  }

  def replace(proof: LKProof, subproof: LKProof, newSubproof: LKProof) : LKProof = {
    if (proof == subproof) newSubproof
    else proof match {
      case Axiom(_) => proof
      case WeakeningLeftRule(up, _, pf) => WeakeningLeftRule(replace(up, subproof, newSubproof), pf.formula)
      case WeakeningRightRule(up, _, pf) => WeakeningRightRule(replace(up, subproof, newSubproof), pf.formula)
      case ContractionLeftRule(up, _, aux, _, _) => ContractionLeftRule(replace(up, subproof, newSubproof), aux.formula)
      case ContractionRightRule(up, _, aux, _, _) => ContractionRightRule(replace(up, subproof, newSubproof), aux.formula)
      case AndRightRule(up1, up2, _, aux1, aux2, _) =>
        if (up1.contains(subproof)) AndRightRule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula)
        else AndRightRule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        AndRightRule(p1, p2, aux1.formula, aux2.formula)*/
      case AndLeft1Rule(up, _, aux, prin) => prin.formula match {
        case And(aux.formula, f) => AndLeft1Rule(replace(up, subproof, newSubproof), aux.formula, f)
      }
      case AndLeft2Rule(up, _, aux, prin) => prin.formula match {
        case And(f, aux.formula) => AndLeft2Rule(replace(up, subproof, newSubproof), f, aux.formula)
      }
      case OrLeftRule(up1, up2, _, aux1, aux2, _) =>
        if (up1.contains(subproof)) OrLeftRule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula)
        else OrLeftRule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        OrLeftRule(p1, p2, aux1.formula, aux2.formula)*/
      case OrRight1Rule(up, _, aux, prin) => prin.formula match {
        case Or(aux.formula, f) => OrRight1Rule(replace(up, subproof, newSubproof), aux.formula, f)
      }
      case OrRight2Rule(up, _, aux, prin) => prin.formula match {
        case Or(f, aux.formula) => OrRight2Rule(replace(up, subproof, newSubproof), f, aux.formula)
      }
      case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>
        if (up1.contains(subproof)) ImpLeftRule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula)
        else ImpLeftRule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        ImpLeftRule(p1, p2, aux1.formula, aux2.formula)*/
      case ImpRightRule(up, _, aux1, aux2, _) => ImpRightRule(replace(up, subproof, newSubproof), aux1.formula, aux2.formula)
      case NegLeftRule(up, _, aux, _) => NegLeftRule(replace(up, subproof, newSubproof), aux.formula)
      case NegRightRule(up, _, aux, _) => NegRightRule(replace(up, subproof, newSubproof), aux.formula)
      case ForallLeftRule(up, _, aux, prin, term) => ForallLeftRule(replace(up, subproof, newSubproof), aux.formula, prin.formula, term)
      case ForallRightRule(up, _, aux, prin, eigenVar) => ForallRightRule(replace(up, subproof, newSubproof), aux.formula, prin.formula, eigenVar)
      case ExistsLeftRule(up, _, aux, prin, eigenVar) => ExistsLeftRule(replace(up, subproof, newSubproof), aux.formula, prin.formula, eigenVar)
      case ExistsRightRule(up, _, aux, prin, term) => ExistsRightRule(replace(up, subproof, newSubproof), aux.formula, prin.formula, term)
      case DefinitionLeftRule(up, _, aux, prin) => DefinitionLeftRule(replace(up, subproof, newSubproof), aux.formula, prin.formula)
      case DefinitionRightRule(up, _, aux, prin) => DefinitionRightRule(replace(up, subproof, newSubproof), aux.formula, prin.formula)
      case EquationLeft1Rule(up1, up2, _, aux1, aux2, prin) =>
        if (up1.contains(subproof)) EquationLeft1Rule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula, prin.formula)
        else EquationLeft1Rule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula, prin.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        EquationLeft1Rule(p1, p2, aux1.formula, aux2.formula, prin.formula)*/
      case EquationLeft2Rule(up1, up2, _, aux1, aux2, prin) =>
        if (up1.contains(subproof)) EquationLeft2Rule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula, prin.formula)
        else EquationLeft2Rule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula, prin.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        EquationLeft2Rule(p1, p2, aux1.formula, aux2.formula, prin.formula)*/
      case EquationRight1Rule(up1, up2, _, aux1, aux2, prin) =>
        if (up1.contains(subproof)) EquationRight1Rule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula, prin.formula)
        else EquationRight1Rule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula, prin.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        EquationRight1Rule(p1, p2, aux1.formula, aux2.formula, prin.formula)*/
      case EquationRight2Rule(up1, up2, _, aux1, aux2, prin) =>
        if (up1.contains(subproof)) EquationRight2Rule(replace(up1, subproof, newSubproof), up2, aux1.formula, aux2.formula, prin.formula)
        else EquationRight2Rule(up1, replace(up2, subproof, newSubproof), aux1.formula, aux2.formula, prin.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        EquationRight2Rule(p1, p2, aux1.formula, aux2.formula, prin.formula)*/
      case CutRule(up1, up2, _, aux1, aux2) =>
        if (up1.contains(subproof)) CutRule(replace(up1, subproof, newSubproof), up2, aux1.formula)
        else CutRule(up1, replace(up2, subproof, newSubproof), aux1.formula)
 /*       val p1 = replace(up1, subproof, newSubproof)
        val p2 = replace(up2, subproof, newSubproof)
        CutRule(p1, p2, aux1.formula)*/
    }
  }
}

// returns a List[LKProof] of all the cuts
// in an LKProof
object getCutsAsProofs {
  def apply(p:LKProof) : List[LKProof] = p match {
    case CutRule(p1,p2,root,aux1,aux2) => apply(p1) ++ apply(p2) ++ List(p)
    case x : NullaryLKProof => Nil
    case UnaryLKProof(_, p1, _, _, _ ) => apply(p1)
    case BinaryLKProof(_, p1, p2, _, _, _, _) => apply(p1) ++ apply(p2)
    // support LKsk
    case UnaryLKskProof(_,p,_,_,_) => apply(p)
    // support SLK
    case UnarySchemaProof(_,p,_,_,_) => apply(p)
    case SchemaProofLinkRule(_, _, _) => Nil
    case _ => throw new Exception("Unkown LK rule in extraction of cut-forumlas from proof! ")
  }
}

object cutformulaExtraction {
  def apply(p:LKProof) = getCutFormulas(p)

  def getCutFormulas(p:LKProof) : List[Sequent] = {
    getCutsAsProofs(p) map ((x: LKProof) =>
      x match { case CutRule(_,_,_,aux,_) => Sequent(Nil, List(aux)) }
      )
  }
}

// Adds weakenings to p in order to obtain the sequent s as the end-sequent.
// Note: s should be a super-set of p's end-sequent.
object addWeakenings {
  def apply(p: LKProof, s: FSequent) = {
    val root_ant = p.root.antecedent.map(x => x.formula)
    val root_suc = p.root.succedent.map(x => x.formula)
    val s_ant = s.antecedent
    val s_suc = s.succedent

    assert(root_ant.forall(e => s_ant.contains(e)) && root_suc.forall(e => s_suc.contains(e)))

    // Take formulas that occur in s and do not occur in p's end-sequent
    val diff_ant = s_ant.diff(root_ant) 
    val diff_suc = s_suc.diff(root_suc)

    // Add weakenings left
    val wl = diff_ant.foldRight(p) {case (f, proof) =>
      WeakeningLeftRule(proof, f)
    }
    // Add weakenings right
    diff_suc.foldRight(wl) {case (f, proof) =>
      WeakeningRightRule(proof, f)
    }
  }
}

// Adds contractions to p in order to obtain the sequent s as the end-sequent.
// Note: s should be a sub-set of p's end-sequent.
object addContractions {
  def apply(p: LKProof, s: FSequent) = {
    val root_ant = p.root.antecedent.map(x => x.formula)
    val root_suc = p.root.succedent.map(x => x.formula)
    val s_ant = s.antecedent
    val s_suc = s.succedent

    assert(s_ant.forall(e => root_ant.contains(e)) && s_suc.forall(e => root_suc.contains(e)))

    // Take formulas that occur in p's end sequent and do not occur in s
    val diff_ant = root_ant.diff(s_ant)
    val diff_suc = root_suc.diff(s_suc)

    // Add contractions left
    val wl = diff_ant.foldRight(p) {case (f, proof) =>
      ContractionLeftRule(proof, f)
    }
    // Add contractions right
    diff_suc.foldRight(wl) {case (f, proof) =>
      ContractionRightRule(proof, f)
    }
  }
}

