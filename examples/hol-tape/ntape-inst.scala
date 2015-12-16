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

import java.nio.file.{Paths, Files}

import at.logic.gapt.expr.hol._

import at.logic.gapt.formats.arithmetic.HOLTermArithmeticalExporter
import at.logic.gapt.formats.hlk.HLKHOLParser
import at.logic.gapt.formats.latex.SequentsListLatexExporter

import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.formats.tptp.TPTPHOLExporter
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld.base.HOLSequentOrdering
import at.logic.gapt.proofs.lkOld._

import at.logic.gapt.proofs.ceres.clauseSets._
import at.logic.gapt.proofs.ceres.struct.StructCreators

object exportLatex {
  def apply( list: List[HOLSequent], fn: String ) = {
    val writer = ( new FileWriter( fn ) with SequentsListLatexExporter with HOLTermArithmeticalExporter )
    writer.exportSequentList( list, Nil ).close
  }
}

object exportTHF {
  def apply( ls: List[HOLSequent], filename: String, positive: Boolean = false ) =
    Files.write(Paths.get(filename), TPTPHOLExporter( ls, positive ).getBytes)
}

 val nLine = sys.props("line.separator")

 def show(s:String) = println( nLine + nLine + "+++++++++ "+s+" ++++++++++" + nLine )

 show("Loading file")
 val pdb = HybridLatexParser(filename)

 show("Eliminating definitions, expanding tautological axioms")
 val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))

 show("Skolemizing")
 val selp = LKToLKsk(elp)

 show("Extracting struct")
 val struct = StructCreators.extract(selp, x => containsQuantifierOnLogicalLevel(x) || freeHOVariables(x).nonEmpty)

 show("Computing clause set")
 //val cl = AlternativeStandardClauseSet(struct)
 val cl = SimpleStandardClauseSet(struct)
 //val cl = StandardClauseSet.transformStructToClauseSet(struct).map(_.toHOLSequent)

 show("simplifying clause set")
 val fs = HOLSequent(Nil, List(HLKHOLParser.parseFormula("var x :i; x = x")))
 val rcl = subsumedClausesRemovalHOL(fs::(cl.toList))
 val tcl = deleteTautologies(rcl)

 show("exporting to THF and Tex")
 exportTHF(tcl.sorted(HOLSequentOrdering), filename+".tptp")
 exportLatex(tcl.sorted(HOLSequentOrdering), filename+".tex")

 show("statistics")
 println("Clause set:"+cl.size)
 println("Reduced clause set:"+tcl.size)
