/* Rewriting on Formulas on Sequent Calclus Proofs */


package at.logic.algorithms.rewriting

import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.lk.definitionRules.{DefinitionRightRule, DefinitionLeftRule}
import at.logic.calculi.lk.equationalRules.{EquationRight2Rule, EquationRight1Rule, EquationLeft2Rule, EquationLeft1Rule}
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules.{ExistsRightRule, ExistsLeftRule, ForallRightRule, ForallLeftRule}
import at.logic.calculi.occurrences.{defaultFormulaOccurrenceFactory, FormulaOccurrence}
import at.logic.language.hol._

object Util {
  class ElimEx(val uproofs : List[LKProof], val aux : List[FormulaOccurrence], val prim : HOLFormula, val defs : Option[Map[FormulaOccurrence, FormulaOccurrence]] ) extends Exception {
    override def getMessage() = {
      var s = ("proofs:\n\n")
      for (p <- uproofs)
        s = s + p.toString() + "\n"
      s = s + "\nauxiliary formulas:\n\n"
      for (p <- aux)
        s = s + p.toString() + "\n"
      s = s + "\nprimary formula:\n"+ prim +"\n"

      s
    }
  }

  //debugging stuff
  def print_hashcodes(msg: String, s:Sequent) = {
    println(msg)
    println(s)
    print(s.antecedent map  ((x:FormulaOccurrence) => x.id))
    print(" :- ")
    print(s.succedent map  ((x:FormulaOccurrence) => x.id))
    println
  }

  def print_hashcodes(msg: String, m : Map[FormulaOccurrence, FormulaOccurrence]) = {
    println(msg)
    println(m)
    println(m map ((x:(FormulaOccurrence,FormulaOccurrence)) => (x._1.id,x._2.id)))
  }


  def check_map(map : Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof) : Boolean = {
    val ant = proof.root.antecedent
    val succ = proof.root.succedent
    for (el <- map.values) {
      println("searching for "+System.identityHashCode(el))
      if ((! ant.contains(el)) && (! succ.contains(el)))
        throw new ElimEx(proof::Nil, el::Nil, el.formula, Some(map))
    }
    true
  }

  def check_map(map : Map[FormulaOccurrence, FormulaOccurrence], proof: LKProof, dproof : LKProof) : Boolean =
    check_map(map, proof.root, dproof.root)


  def check_map(map : Map[FormulaOccurrence, FormulaOccurrence], root: Sequent, droot : Sequent) : Boolean = {
    var error = false
    for (fo <- root.antecedent) {
      if (! (map.keySet contains fo)) {
        println("PROBLEM: map does not contain "+fo.id)
        error = true
      }
      else
      if (! (droot.antecedent contains map(fo))) {
        println("PROBLEM: FO #" + fo.id, " maps to "+map(fo).id + ", but is not present in antecedent of new root!")
        error = true
      }
    }
    for (fo <- root.succedent) {
      if (! (map.keySet contains fo)) {
        println("PROBLEM: map does not contain "+fo.id)
        error = true
      }
      else
      if (! (droot.succedent contains map(fo))) {
        println("PROBLEM: FO #" + fo.id, " maps to "+map(fo).id + ", but is not present in succedent of new root!")
        error = true
      }
    }

    if (error) {
      print_hashcodes("Original Proof:", root )
      print_hashcodes("Modified Proof:", droot )
      print_hashcodes("Map:", map )
    }

    error
  }
 //fsequent2sequent
  def f2focc(f:HOLFormula) = new FormulaOccurrence(f, Nil, defaultFormulaOccurrenceFactory)
  def fsequent2sequent(s : FSequent) = Sequent(s._1 map f2focc , s._2 map f2focc )

}

object DefinitionElimination {
  import Util._
  private val emptymap = Map[FormulaOccurrence,FormulaOccurrence]() //this will be passed to some functions


  private def c(e:HOLExpression) = {
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")
  }

  //eliminates defs in proof and returns a mapping from the old aux formulas to the new aux formulas
  // + the proof with the definition removed
  def eliminate_in_proof_(rewrite : (HOLExpression => HOLExpression), proof : LKProof) :
  (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    proof match {
      // introductory rules
      case Axiom(Sequent(antecedent, succedent)) =>
        println("Axiom!")
        val antd  =  antecedent.map((x:FormulaOccurrence) => c(rewrite(x.formula)))  //recursive_elimination_from(defs,antecedent.map((x:FormulaOccurrence) => x.formula))
        val succd =  succedent.map((x:FormulaOccurrence) => c(rewrite(x.formula))) //recursive_elimination_from(defs,succedent.map((x:FormulaOccurrence) => x.formula))
        val dproof = Axiom(antd, succd)
        val correspondences = calculateCorrespondences(Sequent(antecedent, succedent) , dproof)

        check_map(correspondences, proof, dproof)

        (correspondences, dproof)

      /* in the following part, dmap[1,2] holds the old correspondences of the upper subproof(s), needed to map the auxiliary formulas to the
* ones with removed definitions; correspondences holds the new mapping. */
      //structural rules
      case CutRule(uproof1,uproof2,root,aux1,aux2) =>
        println("Cut!")
        val (dmap1,duproof1) = eliminate_in_proof_(rewrite, uproof1)
        val (dmap2,duproof2) = eliminate_in_proof_(rewrite, uproof2)
        //val correspondences1 = calculateCorrespondences(defs, emptymap, root, duproof1)
        //val correspondences2 = calculateCorrespondences(defs, correspondences1, root, duproof2)

        val dproof = CutRule(duproof1,  duproof2,  dmap1(aux1), dmap2(aux2))
        val correspondences = calculateCorrespondences(root, dproof)
        (correspondences, dproof )

      case WeakeningLeftRule(uproof, root, prin) =>
        println("Weakening Left!")
        handleWeakeningRule(rewrite, uproof, root, prin, WeakeningLeftRule.apply)

      case WeakeningRightRule(uproof, root, prin) =>
        println("Weakening Right!")
        handleWeakeningRule(rewrite, uproof, root, prin, WeakeningRightRule.apply)

      case ContractionLeftRule(uproof, root, aux1, aux2, prim) =>
        println("Contraction Left!")
        handleContractionRule(rewrite, uproof, root, aux1, aux2, ContractionLeftRule.apply)

      case ContractionRightRule(uproof, root, aux1, aux2, prim) =>
        println("Contraction Right!")
        handleContractionRule(rewrite, uproof, root, aux1, aux2, ContractionRightRule.apply)

      //logical rules
      case NegLeftRule(uproof, root, aux, prin)  =>
        println("Negation Left!")
        handleNegationRule(rewrite, uproof, root, aux, NegLeftRule.apply)

      case NegRightRule(uproof, root, aux, prin)  =>
        println("Negation Right!")
        handleNegationRule(rewrite, uproof, root, aux, NegRightRule.apply)

      case AndLeft1Rule(uproof, root, aux, prin)  =>
        println("And 1 Left!")
        handleUnaryLogicalRule(rewrite, uproof, root, aux, prin, AndLeft1Rule.apply )

      case AndLeft2Rule(uproof, root, aux, prin)  =>
        println("And 2 Left!")
        handleUnaryLogicalRule(rewrite, uproof, root, aux, prin, switchargs(AndLeft2Rule.apply) )

      case AndRightRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        println("And Right")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, AndRightRule.apply)

      case OrRight1Rule(uproof, root, aux, prin)  =>
        println("Or 1 Right")
        handleUnaryLogicalRule(rewrite, uproof, root, aux, prin, OrRight1Rule.apply )

      case OrRight2Rule(uproof, root, aux, prin)  =>
        println("Or 2 Right")
        handleUnaryLogicalRule(rewrite, uproof, root, aux, prin, switchargs(OrRight2Rule.apply) )

      case OrLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        println("Or Left!")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, OrLeftRule.apply)

      case ImpLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        println("Imp Left")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, ImpLeftRule.apply)

      case ImpRightRule(uproof, root, aux1, aux2, prin)  =>
        println("Imp Right")
        val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
        val dproof = ImpRightRule(duproof, dmap(aux1), dmap(aux2)  )
        val correspondences = calculateCorrespondences(root, duproof)
        (correspondences,  dproof)

      //quantfication rules
      case ForallLeftRule(uproof, root, aux, prim, substituted_term) =>
        println("Forall Left")
        handleWeakQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ForallLeftRule.apply)
      case ForallRightRule(uproof, root, aux, prim, substituted_term) =>
        println("Forall Right")
        handleStrongQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ForallRightRule.apply)
      case ExistsLeftRule(uproof, root, aux, prim, substituted_term) =>
        println("Exists Left")
        handleStrongQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ExistsLeftRule.apply)
      case ExistsRightRule(uproof, root, aux, prim, substituted_term) =>
        println("Exists Right")
        handleWeakQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ExistsRightRule.apply)

      //equational rules
      case EquationLeft1Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
        println("Equation Left 1")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationLeft1Rule.apply)
      case EquationLeft2Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
        println("Equation Left 2")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationLeft2Rule.apply)
      case EquationRight1Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
        println("Equation Right 1")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationRight1Rule.apply)
      case EquationRight2Rule(uproof1, uproof2, root, aux1, aux2, prim) =>
        println("Equation Right 2")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationRight2Rule.apply)

      //definition rules
      case DefinitionLeftRule(uproof, root, aux, prin) =>
        println("Def Left")
        handleDefinitionRule(rewrite, uproof, root, aux, prin, DefinitionLeftRule.apply)


      case DefinitionRightRule(uproof, root, aux, prin) =>
        println("Def Right")
        handleDefinitionRule(rewrite, uproof, root, aux, prin, DefinitionRightRule.apply)

    }

  }

  // ------ helper functions for rewriting



  def handleWeakeningRule(rewrite : (HOLExpression => HOLExpression),
                          uproof: LKProof, root: Sequent, prin: FormulaOccurrence,
                          createRule : (LKProof,  HOLFormula) => LKProof )
  : (Map[FormulaOccurrence,FormulaOccurrence], LKProof) = {
    val (dmap, duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, c(rewrite(prin.formula)))
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences, dproof)
  }

  def handleContractionRule(rewrite : (HOLExpression => HOLExpression),
                            uproof: LKProof,
                            root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                            createRule : (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap, duproof) = eliminate_in_proof_(rewrite, uproof)
    println("Contracting from: "+aux1+" and "+ aux2)
    println("Contracting to:   "+dmap(aux1)+" and "+ dmap(aux2))
    throw new ElimEx(uproof::duproof::Nil, aux1::aux2::Nil, uproof.root.toFormula, Some(dmap))

    val dproof = createRule(duproof, dmap(aux1), dmap(aux2))
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences, dproof)
  }

  def handleNegationRule(rewrite : (HOLExpression => HOLExpression), uproof: LKProof, root: Sequent,
                         aux: FormulaOccurrence,
                         createRule : (LKProof, FormulaOccurrence) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, dmap(aux) )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }

  //only handles AndL1,2 and OrR1,2 -- ImpR and NegL/R are different
  def handleUnaryLogicalRule(rewrite : (HOLExpression => HOLExpression), uproof: LKProof, root: Sequent,
                             aux: FormulaOccurrence, prin : FormulaOccurrence,
                             createRule : (LKProof, FormulaOccurrence, HOLFormula) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, dmap(aux), c(rewrite(prin.formula))  )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }


  def handleBinaryLogicalRule(rewrite : (HOLExpression => HOLExpression), uproof1: LKProof, uproof2: LKProof,
                              root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                              prin : FormulaOccurrence,
                              createRule : (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap1,duproof1) = eliminate_in_proof_(rewrite, uproof1)
    val (dmap2,duproof2) = eliminate_in_proof_(rewrite, uproof2)

    val dproof = createRule(duproof1, duproof2, dmap1(aux1), dmap2(aux2)  )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }


  def handleWeakQuantifierRule(rewrite : (HOLExpression => HOLExpression), uproof: LKProof, root: Sequent,
                                               aux: FormulaOccurrence, prin : FormulaOccurrence, substituted_term : HOLExpression,
                                               createRule : (LKProof, FormulaOccurrence, HOLFormula, HOLExpression) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, dmap(aux), c(rewrite(prin.formula)),  rewrite(substituted_term)   )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }

  def handleStrongQuantifierRule(rewrite : (HOLExpression => HOLExpression), uproof: LKProof, root: Sequent,
                           aux: FormulaOccurrence, prin : FormulaOccurrence, eigenvar : HOLVar,
                           createRule : (LKProof, FormulaOccurrence, HOLFormula, HOLVar) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, dmap(aux), c(rewrite(prin.formula)),  eigenvar  )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }


  def handleEquationalRule(rewrite : (HOLExpression => HOLExpression), uproof1: LKProof, uproof2: LKProof,
                           root: Sequent, aux1: FormulaOccurrence, aux2: FormulaOccurrence,
                           prin : FormulaOccurrence,
                           createRule : (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap1,duproof1) = eliminate_in_proof_(rewrite, uproof1)
    val (dmap2,duproof2) = eliminate_in_proof_(rewrite, uproof2)
    val ucorrespundences = (dmap1 ++ dmap2)

    val dproof = createRule(duproof1, duproof2, dmap1(aux1), dmap2(aux2) , ucorrespundences(prin).formula )
    val correspondences = calculateCorrespondences(root, dproof)
    (correspondences,  dproof)
  }

  def handleDefinitionRule(rewrite : (HOLExpression => HOLExpression), uproof: LKProof, root: Sequent,
                           aux: FormulaOccurrence, prin : FormulaOccurrence,
                           createRule : (LKProof, FormulaOccurrence, HOLFormula) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)

    val correspondences_toparent =
      NameReplacement.find_matching[FormulaOccurrence, FormulaOccurrence](root.occurrences.toList, uproof.root.occurrences.toList,
        (occ1, occ2) => {
          if (occ1 == prin) occ2 == aux else
            occ1.formula syntaxEquals occ2.formula
        } )

    val dmapnew = correspondences_toparent.map(x => (x._1, dmap(x._2)))

    //we skip the rule, so current occurrences have to be mapped to what their ancestors were
    //val dmapnew = Map[FormulaOccurrence,FormulaOccurrence]() ++
    //  (uproof.root.occurrences flatMap (_.ancestors.map (x => (x, dmap.getOrElse(x, throw new Exception("Could not find fo "+x+" in map "+ (dmap.keys.mkString(", ")) ))))))
    (dmapnew, duproof)
  }


  /* calculates the correspondences between occurences of the formulas in the original end-sequent and those in the
*  definition free one. in binary rules, ancestors may occur in both branches, so we also pass a map with previously
*  calculated correspondences and add the new ones */
  private def calculateCorrespondences(//defs: definitions.DefinitionsMap,
                                       root: Sequent, duproof: LKProof)
  : Map[FormulaOccurrence, FormulaOccurrence] = {
    val r = emptymap ++ (root.antecedent zip duproof.root.antecedent) ++ (root.succedent zip duproof.root.succedent)
    print_hashcodes("DEBUG: Correspondences", r)
    r
  }

  //switches arguments such that the apply methods of AndL1,2 and OrL1,2 have the same signature
  def switchargs[A,B,C,D](f : (A, B, C) => D) : ((A, C ,B) => D) = ((a:A, c:C ,b:B) => f(a,b,c))




}
