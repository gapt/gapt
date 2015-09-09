/* *************************************************************************** *
   n-Tape Proof script: loads an instance of the n-Tape proof, extracts the
   characteristic sequent set and exports it to tptp.
   Usage:                                                                       
     (start cli in gapt/source directory or adjust the filename variable below command)     
     :load examples/hol-tape/ntape-inst.scala                               
     prooftool(acnf)                                                            
                                                                                
 * *************************************************************************** */

/* adjust filename to load a different example */
//val filename = "tape3-4c.llk"  
val filename = "examples/hol-tape/tape3-3.llk"  

/* begin of proof script  */

import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary._
import at.logic.gapt.expr.fol.{undoHol2Fol, replaceAbstractions, reduceHolToFol}
import at.logic.gapt.expr.hol._

import at.logic.gapt.expr.fol.undoHol2Fol

import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk.base.HOLSequentOrdering
import at.logic.gapt.proofs.lk.{AtomicExpansion, regularize, subsumedClausesRemovalHOL}
import at.logic.gapt.proofs.lksk.sequentToLabelledSequent
import at.logic.gapt.proofs.resolutionOld.RobinsonToRal

import at.logic.gapt.provers.prover9._
import at.logic.gapt.proofs.ceres.clauseSets._
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators

import at.logic.gapt.proofs.ceres.ceres_omega
import at.logic.gapt.proofs.lksk.LKskToExpansionProof
import at.logic.gapt.proofs.lk.LKToLKsk

 val nLine = sys.props("line.separator")

 def show(s:String) = println( nLine + nLine + "+++++++++ "+s+" ++++++++++" + nLine )

 show("Loading file")
 val pdb = loadLLK(filename)

 show("Eliminating definitions, expanding tautological axioms")
 val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))

 show("Skolemizing")
 val selp = LKToLKsk(elp)

 show("Extracting struct")
 val struct = StructCreators.extract(selp, x => containsQuantifierOnLogicalLevel(x) || freeHOVariables(x).nonEmpty)

 show("Computing clause set")
 //val cl = AlternativeStandardClauseSet(struct)
 val cl = SimpleStandardClauseSet(struct)
 //val cl = structToClausesList(struct).map(_.toHOLSequent)

 show("simplifying clause set")
 val fs = HOLSequent(Nil, List(parseLLKFormula("var x :i; x = x")))
 val rcl = subsumedClausesRemovalHOL(fs::(cl.toList))
 val tcl = deleteTautologies(rcl)

 show("exporting to THF and Tex")
 exportTHF(tcl.sorted(HOLSequentOrdering), filename+".tptp")
 exportLatex(tcl.sorted(HOLSequentOrdering), filename+".tex")

 show("statistics")
 println("Clause set:"+cl.size)
 println("Reduced clause set:"+tcl.size)
