package at.logic.algorithms.rewriting

import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol._
import at.logic.language.lambda.symbols.{SymbolA, StringSymbol}
import at.logic.algorithms.matching.NaiveIncompleteMatchingAlgorithm
import at.logic.language.fol.FOLFormula
import at.logic.calculi.lk._
import at.logic.algorithms.lk.AtomicExpansion
import Util._


object DefinitionElimination extends DefinitionElimination
class DefinitionElimination {
  type DefinitionsMap = Map[HOLExpression, HOLExpression]
  type ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]

  def apply(dmap : DefinitionsMap, f:HOLFormula) : HOLFormula = {
    val edmap = expand_dmap(dmap)
    replaceAll_informula(edmap, f)
  }

  def apply(dmap : DefinitionsMap, f:HOLExpression) : HOLExpression = {
    val edmap = expand_dmap(dmap)
    replaceAll_in(edmap, f)
  }

  def apply(dmap : DefinitionsMap, p:LKProof) : LKProof = {
    val edmap = expand_dmap(dmap)
    eliminate_in_proof(replaceAll_in(edmap,_),p)
  }
  
  def fixedpoint_val[A](f : (A=>A), l : A) : A = {
    val r = f(l)
    if (r==l) r  else fixedpoint_val(f,r)
  }

  def fixedpoint_seq[A](f : (A=>A), l : Seq[A] ) : Seq[A] = {
    val r = l map f
    if (r==l) r  else fixedpoint_seq(f,r)
  }

  private def c(e:HOLExpression) = {
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")
  }

  def replaceAll_informula(dmap: DefinitionsMap, e:HOLFormula) : HOLFormula = c(replaceAll_in(dmap,e))
  def replaceAll_in(dmap : DefinitionsMap, e : HOLExpression) : HOLExpression = {
    e match {
      case HOLConst(_,_) => try_to_match(dmap, e)
      case HOLVar(_,_) => try_to_match(dmap, e)
      case Neg(s) => Neg(replaceAll_informula(dmap,s))
      case And(s,t) => And(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      case Or(s,t) => Or(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      case Imp(s,t) => Imp(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      case AllVar(x,t) => AllVar(x, replaceAll_informula(dmap, t))
      case ExVar(x,t) => ExVar(x, replaceAll_informula(dmap, t))
      case HOLApp(s,t) =>
        val fullmatch = try_to_match(dmap,e)
        if (fullmatch == e)
          try_to_match(dmap,e.factory.createApp(replaceAll_in(dmap, s), replaceAll_in(dmap,t)).asInstanceOf[HOLExpression])
        else
          replaceAll_in(dmap,fullmatch)
      case HOLAbs(x,t) => e.factory.createAbs(x, replaceAll_in(dmap, t)).asInstanceOf[HOLExpression]
    }
  }


  def try_to_matchformula(dmap:DefinitionsMap,e:HOLExpression) = c(try_to_match(dmap,e))
  def try_to_match(dmap: DefinitionsMap, e: HOLExpression): HOLExpression = {
    dmap.keys.foldLeft(e)((v, key) => {
//      println("matching " + v + " against " + key)
      NaiveIncompleteMatchingAlgorithm.holMatch(key, v)(Nil) match {
        case None => v
        case Some(sub) =>
          val r = sub(dmap(key))
//          println("YES! "+sub)
          r
      }
    }
    )
  }

  def expand_dmap(dmap: DefinitionsMap) : DefinitionsMap = {
    val ndmap = dmap map ( x => {
      (x._1, replaceAll_in(dmap, x._2))
    })

    if (ndmap == dmap)
      dmap
    else expand_dmap(ndmap)
  }

  private def eliminate_from_(defs : ProcessedDefinitionsMap, f : HOLFormula) : HOLFormula = {
    f match {
      case Atom(e, args) => {
          val sym = e match {
            case v : HOLVar => v.sym
            case c : HOLConst => c.sym
          }

          defs.get(sym) match {
            case Some((definition_args, defined_formula)) =>
              if (args.length != definition_args.length) {
                println("Warning: ignoring definition replacement because argument numbers dont match!")
                f
              } else {
                //we need to insert the correct values for the free variables in the definition
                //the casting is needed since we cannot make a map covariant
                //val pairs = (definition_args zip args)  filter ((x:(HOLExpression, HOLExpression) ) => x._1.isInstanceOf[HOLVar])
                val pairs = definition_args zip  args
                val sub = Substitution(pairs)
                println("Substitution:")
                println(sub)
                sub.apply(defined_formula).asInstanceOf[HOLFormula]
              }
            case _ => f
          }
        }
      case Neg(f1) => Neg(eliminate_from_(defs, f1))
      case AllVar(q,f1) => AllVar(q, eliminate_from_(defs, f1))
      case ExVar(q,f1) => ExVar(q, eliminate_from_(defs, f1))
      case And(f1,f2) => And(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case Imp(f1,f2) => Imp(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case Or(f1,f2)  => Or(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case _ => println("Warning: unhandled case in definition elimination!"); f
    }
  }

  private val emptymap = Map[FormulaOccurrence,FormulaOccurrence]() //this will be passed to some functions
  private def debug(s:String) = { }

  def eliminate_in_proof(rewrite : (HOLExpression => HOLExpression), proof : LKProof) : LKProof =
    eliminate_in_proof_(rewrite,proof)._2

  //eliminates defs in proof and returns a mapping from the old aux formulas to the new aux formulas
  // + the proof with the definition removed
  def eliminate_in_proof_(rewrite : (HOLExpression => HOLExpression), proof : LKProof) :
  (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    proof match {
      // introductory rules
      case Axiom(Sequent(antecedent, succedent)) =>
        debug("Axiom!")
        val antd  =  antecedent.map((x:FormulaOccurrence) => c(rewrite(x.formula)))  //recursive_elimination_from(defs,antecedent.map((x:FormulaOccurrence) => x.formula))
      val succd =  succedent.map((x:FormulaOccurrence) => c(rewrite(x.formula))) //recursive_elimination_from(defs,succedent.map((x:FormulaOccurrence) => x.formula))
      //val dproof = Axiom(antd, succd)
      val dproof = Axiom(antd,succd)
        val correspondences = calculateCorrespondences(Sequent(antecedent, succedent) , dproof)

        check_map(correspondences, proof, dproof)

        (correspondences, dproof)

      /* in the following part, dmap[1,2] holds the old correspondences of the upper subproof(s), needed to map the auxiliary formulas to the
* ones with removed definitions; correspondences holds the new mapping. */
      //structural rules
      case CutRule(uproof1,uproof2,root,aux1,aux2) =>
        debug("Cut!")
        val (dmap1,duproof1) = eliminate_in_proof_(rewrite, uproof1)
        val (dmap2,duproof2) = eliminate_in_proof_(rewrite, uproof2)
        debug("aux:  "+aux1+" and "+aux2)
        debug("daux: "+dmap1(aux1)+" and "+dmap2(aux2))

        val dproof = CutRule(duproof1,  duproof2,  dmap1(aux1), dmap2(aux2))
        val correspondences = calculateCorrespondences(root, dproof)
        (correspondences, dproof )

      case WeakeningLeftRule(uproof, root, prin) =>
        debug("Weakening Left!")
        handleWeakeningRule(rewrite, uproof, root, prin, WeakeningLeftRule.apply)

      case WeakeningRightRule(uproof, root, prin) =>
        debug("Weakening Right!")
        handleWeakeningRule(rewrite, uproof, root, prin, WeakeningRightRule.apply)

      case ContractionLeftRule(uproof, root, aux1, aux2, prim) =>
        debug("Contraction Left!")
        handleContractionRule(rewrite, uproof, root, aux1, aux2, ContractionLeftRule.apply)

      case ContractionRightRule(uproof, root, aux1, aux2, prim) =>
        debug("Contraction Right!")
        handleContractionRule(rewrite, uproof, root, aux1, aux2, ContractionRightRule.apply)

      //logical rules
      case NegLeftRule(uproof, root, aux, prin)  =>
        debug("Negation Left!")
        handleNegationRule(rewrite, uproof, root, aux, NegLeftRule.apply)

      case NegRightRule(uproof, root, aux, prin)  =>
        debug("Negation Right!")
        handleNegationRule(rewrite, uproof, root, aux, NegRightRule.apply)

      case AndLeft1Rule(uproof, root, aux, prin)  =>
        debug("And 1 Left!")
        val vf = prin.formula match { case And(_,x) => x }
        handleUnaryLogicalRule(rewrite, uproof, root, aux, vf, AndLeft1Rule.apply )

      case AndLeft2Rule(uproof, root, aux, prin)  =>
        debug("And 2 Left!")
        val vf = prin.formula match { case And(x,_) => x }
        handleUnaryLogicalRule(rewrite, uproof, root, aux, vf, switchargs(AndLeft2Rule.apply) )

      case AndRightRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        debug("And Right")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, AndRightRule.apply)

      case OrRight1Rule(uproof, root, aux, prin)  =>
        debug("Or 1 Right")
        val vf = prin.formula match { case Or(_,x) => x }
        handleUnaryLogicalRule(rewrite, uproof, root, aux, vf, OrRight1Rule.apply )

      case OrRight2Rule(uproof, root, aux, prin)  =>
        debug("Or 2 Right")
        val vf = prin.formula match { case Or(x,_) => x }
        handleUnaryLogicalRule(rewrite, uproof, root, aux, vf, switchargs(OrRight2Rule.apply) )

      case OrLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        debug("Or Left!")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, OrLeftRule.apply)

      case ImpLeftRule(uproof1, uproof2, root, aux1, aux2, prin)  =>
        debug("Imp Left")
        handleBinaryLogicalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prin, ImpLeftRule.apply)

      case ImpRightRule(uproof, root, aux1, aux2, prin)  =>
        debug("Imp Right")
        val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
        val dproof = ImpRightRule(duproof, dmap(aux1), dmap(aux2)  )
        val correspondences = calculateCorrespondences(root, dproof)
        (correspondences,  dproof)

      //quantfication rules
      case ForallLeftRule(uproof, root, aux, prim, substituted_term) =>
        debug("Forall Left")
        handleWeakQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ForallLeftRule.apply)
      case ForallRightRule(uproof, root, aux, prim, substituted_term) =>
        debug("Forall Right")
        handleStrongQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ForallRightRule.apply)
      case ExistsLeftRule(uproof, root, aux, prim, substituted_term) =>
        debug("Exists Left")
        handleStrongQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ExistsLeftRule.apply)
      case ExistsRightRule(uproof, root, aux, prim, substituted_term) =>
        debug("Exists Right")
        handleWeakQuantifierRule(rewrite, uproof, root, aux, prim, substituted_term, ExistsRightRule.apply)

      //equational rules
      case EquationLeft1Rule(uproof1, uproof2, root, aux1, aux2, _, prim) =>
        debug("Equation Left 1")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationLeftMacroRule.apply)
      case EquationLeft2Rule(uproof1, uproof2, root, aux1, aux2, _, prim) =>
        debug("Equation Left 2")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationLeftMacroRule.apply)
      case EquationRight1Rule(uproof1, uproof2, root, aux1, aux2, _, prim) =>
        debug("Equation Right 1")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationRightMacroRule.apply)
      case EquationRight2Rule(uproof1, uproof2, root, aux1, aux2, _, prim) =>
        debug("Equation Right 2")
        handleEquationalRule(rewrite, uproof1, uproof2, root, aux1, aux2, prim, EquationRightMacroRule.apply)

      //definition rules
      case DefinitionLeftRule(uproof, root, aux, prin) =>
        debug("Def Left")
        handleDefinitionRule(rewrite, uproof, root, aux, prin, DefinitionLeftRule.apply)


      case DefinitionRightRule(uproof, root, aux, prin) =>
        debug("Def Right")
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
    debug("Contracting from: "+aux1+" and "+ aux2)
    debug("Contracting to:   "+dmap(aux1)+" and "+ dmap(aux2))
    //throw new ElimEx(uproof::duproof::Nil, aux1::aux2::Nil, uproof.root.toFormula, Some(dmap))

    try {
      val dproof = createRule(duproof, dmap(aux1), dmap(aux2))
      val correspondences = calculateCorrespondences(root, dproof)
      (correspondences, dproof)
    } catch {
      case e: Exception =>
        throw new LKUnaryRuleCreationException("Definition elimination failed in contraction rule: "+e.getMessage, duproof, List(dmap(aux1).formula,dmap(aux2).formula))
    }
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
                             aux: FormulaOccurrence, weakened_formula : HOLFormula,
                             createRule : (LKProof, FormulaOccurrence, HOLFormula) => LKProof)
  : (Map[FormulaOccurrence, FormulaOccurrence], LKProof) = {
    val (dmap,duproof) = eliminate_in_proof_(rewrite, uproof)
    val dproof = createRule(duproof, dmap(aux), c(rewrite(weakened_formula))  )
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
    debug("roccs= "+ root.occurrences.map(_.id))
    debug("doccs= "+ duproof.root.occurrences.map(_.id))
    debug("uoccs= "+ uproof.root.occurrences.map(_.id))
    debug("mocc=  "+ dmap.keys.toList.map(_.id))
    debug("aux =  "+ aux.id+ " "+dmap(aux).id)
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
    val dproof = createRule(duproof1, duproof2, dmap1(aux1), dmap2(aux2) , c(rewrite(prin.formula)) )
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
    //print_hashcodes("DEBUG: Correspondences", r)
    r
  }

  //switches arguments such that the apply methods of AndL1,2 and OrL1,2 have the same signature
  def switchargs[A,B,C,D](f : (A, B, C) => D) : ((A, C ,B) => D) = ((a:A, c:C ,b:B) => f(a,b,c))

}

