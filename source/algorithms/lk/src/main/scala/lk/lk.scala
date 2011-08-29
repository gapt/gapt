package at.logic.algorithms.lk

import at.logic.calculi.lk.propositionalRules._
import scala.collection.immutable.{HashSet, Set}
import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}

import at.logic.calculi.lksk.lkskExtractors.{UnaryLKskProof}

import at.logic.calculi.slk._

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus.{Var, freshVar}
import at.logic.language.lambda.substitutions
import substitutions.Substitution

// TODO: we use the toSet method from axiom here to convert a list to a set,
// perhaps refactor this method out of axiom - it seems useful in general
object getCutAncestors {
  def apply( p: LKProof )
    : Set[FormulaOccurrence] = p match {
      case CutRule(p1, p2, _, a1, a2) => getCutAncestors( p1 ) ++ getCutAncestors( p2 ) ++
                                         Axiom.toSet( getAncestors( a1 ) ) ++ Axiom.toSet( getAncestors( a2 ) )
      case UnaryLKProof(_,p,_,_,_) => getCutAncestors( p )
      case BinaryLKProof(_, p1, p2, _, _, _, _) => getCutAncestors( p1 ) ++ getCutAncestors( p2 )
      case Axiom(_) => Set[FormulaOccurrence]()
      // support LKsk
      case UnaryLKskProof(_,p,_,_,_) => getCutAncestors( p )
      // support SLK
      case UnarySchemaProof(_,p,_,_,_) => getCutAncestors( p )
      case SchemaProofLinkRule(_, _, _) => Set[FormulaOccurrence]()
    }
}

object getAncestors {
  def apply( o: FormulaOccurrence ) : List[FormulaOccurrence] =
    o.ancestors.flatMap( a => getAncestors( a ) ) ::: List( o )

  def apply( o: Set[FormulaOccurrence] ) : Set[FormulaOccurrence] =
    o.foldLeft( new HashSet[FormulaOccurrence] )( (res, o) => res ++ apply( o ) )
}

object regularize {
  def apply( p: LKProof ) = rec( p, Set[HOLVar]() )

  def rec( proof: LKProof, vars: Set[HOLVar] ) : (LKProof, Set[HOLVar], Map[FormulaOccurrence, FormulaOccurrence] ) = 
  {
    implicit val factory = PointerFOFactoryInstance
    proof match
    {
      // FIXME: cast!?!
      case r @ CutRule( p1, p2, _, a1, a2 ) => {
        // first left, then right
        val rec1 = rec( p1, vars )
        val rec2 = rec( p2, vars ++ rec1._2 )
        val new_proof = CutRule( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) )
        ( new_proof, rec2._2, computeMap( p1.root.antecedent ++ (p1.root.succedent - a1), r, new_proof, rec1._3 ) ++
                     computeMap( (p2.root.antecedent - a2) ++ p2.root.succedent, r, new_proof, rec2._3 ) )
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
        val ant_occs = so.antecedent.toList
        val succ_occs = so.succedent.toList
        val a = Axiom.createDefault(Sequent(ant_occs.map( fo => fo.formula ), succ_occs.map( fo => fo.formula )) )
        val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
        a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
        a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
        (a._1, vars, map)
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
        val new_parent = rec( p, vars + v )
        val blacklist = new_parent._2
        val (new_proof, new_blacklist, new_map) = if ( blacklist.contains( v ) ) // rename eigenvariable
        {
          // FIXME: casts!?
          val new_var_name = v.name.toString.head + "_"
          val new_var = freshVar( v.exptype, blacklist.asInstanceOf[Set[Var]], (x => new_var_name + x.toString), v ).asInstanceOf[HOLVar]
          val new_new_parent = applySubstitution( new_parent._1, Substitution[HOLExpression]( v, new_var ) )
          val new_map = new_parent._3.clone
          new_map.transform( (k, v) => new_new_parent._2( v ) ) // compose maps
            ( ExistsLeftRule( new_new_parent._1, new_map( a ), m.formula, new_var ), blacklist + new_var, new_map )
        } else
          ( ExistsLeftRule( new_parent._1, new_parent._3( a ), m.formula, v ), blacklist + v, new_parent._3 )
        ( new_proof, new_blacklist, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_map ) )
      }
      case ForallRightRule( p, s, a, m, v ) => {
        val new_parent = rec( p, vars + v )
        val blacklist = new_parent._2
        val (new_proof, new_blacklist, new_map) = if ( blacklist.contains( v ) ) // rename eigenvariable
        {
          // FIXME: casts!?
          val new_var_name = v.name.toString.head + "_"
          val new_var = freshVar( v.exptype, blacklist.asInstanceOf[Set[Var]], (x => new_var_name + x.toString), v ).asInstanceOf[HOLVar]
          val new_new_parent = applySubstitution( new_parent._1, Substitution[HOLExpression]( v, new_var ) )
          val new_map = new_parent._3.clone
          new_map.transform( (k, v) => new_new_parent._2( v ) ) // compose maps
          ( ForallRightRule( new_new_parent._1, new_map( a ), m.formula, new_var ), blacklist + new_var, new_map )
        } else
          ( ForallRightRule( new_parent._1, new_parent._3( a ), m.formula, v ), blacklist + v, new_parent._3 )
        ( new_proof, new_blacklist, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_map ) )
      }
    }
  }

  def handleWeakening( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                       old_parent: LKProof,
                       old_proof: LKProof,
                       vars: Set[HOLVar],
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
                         vars: Set[HOLVar],
                         constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
    ( new_proof, vars, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }

  def handleEquational( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, m :HOLFormula, vars: Set[HOLVar],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) , m )
      ( new_proof, rec2._2, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }

  def handleBinaryProp( r: BinaryLKProof with AuxiliaryFormulas, p1: LKProof, p2: LKProof, a1: FormulaOccurrence, a2: FormulaOccurrence, vars: Set[HOLVar],
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => BinaryLKProof with AuxiliaryFormulas ) = {
       // first left, then right
      val rec1 = rec( p1, vars )
      val rec2 = rec( p2, vars ++ rec1._2 )
      val new_proof = constructor( rec1._1, rec2._1, rec1._3( a1 ), rec2._3( a2 ) )
      ( new_proof, rec2._2, computeMap( p1.root.antecedent ++ p1.root.succedent, r, new_proof, rec1._3 ) ++
                   computeMap( p2.root.antecedent ++ p2.root.succedent, r, new_proof, rec2._3 ) )
  }

  // FIXME: adapted from LKtoLKskc!
  def computeMap( occs: Set[FormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : Map[FormulaOccurrence, FormulaOccurrence]) =
  {
    val map = new HashMap[FormulaOccurrence, FormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get, 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get ) )
    map
  }

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
      case WeakeningLeftRule(up, _, pf) => WeakeningLeftRule.createDefault(replace(up, subproof, newSubproof), pf.formula)
      case WeakeningRightRule(up, _, pf) => WeakeningRightRule.createDefault(replace(up, subproof, newSubproof), pf.formula)
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