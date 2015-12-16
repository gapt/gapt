/* *************************************************************************** *
   n-Tape Proof script: loads the n-Tape proof and creates a proof in atomic    
   cut normal form by applying the CERES_omega method.                          
   Usage:                                                                       
     (start cli in gapt/source directory or adjust the filename variable below command)     
     :load examples/hol-tape/ntape-script.scala                               
     prooftool(acnf)                                                            
                                                                                
 * *************************************************************************** */

/* adjust filename to load a different example */
val filename = "./examples/hol-tape/ntape.llk"  

//val filename = "./examples/hol-tape/ntape.llk"  
//val filename = "tape3old.llk"  

/* begin of proof script  */

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{replaceAbstractions, reduceHolToFol}
import at.logic.gapt.expr.hol._

import at.logic.gapt.expr.fol.undoHol2Fol

import at.logic.gapt.formats.llk.HybridLatexParser
import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.proofs.FOLClause
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkOld.{AtomicExpansion, regularize}
import at.logic.gapt.proofs.lksk.sequentToLabelledSequent
import at.logic.gapt.proofs.resolution.RobinsonToRal

import at.logic.gapt.provers.prover9._
import at.logic.gapt.proofs.ceres.clauseSets._
import at.logic.gapt.proofs.ceres.projections.Projections
import at.logic.gapt.proofs.ceres.struct.StructCreators

import at.logic.gapt.proofs.ceres.ceres_omega
import at.logic.gapt.proofs.lksk.LKskToExpansionProof
import at.logic.gapt.proofs.lkOld.LKToLKsk

 val nLine = sys.props("line.separator")

 def show(s:String) = println( nLine + nLine + "+++++++++ "+s+" ++++++++++" + nLine)

 class Robinson2RalAndUndoHOL2Fol( sig_vars: Map[String, List[Var]],
                                    sig_consts: Map[String, List[Const]],
                                    cmap: replaceAbstractions.ConstantsMap ) extends RobinsonToRal {
    val absmap = Map[String, LambdaExpression]() ++ ( cmap.toList.map( x => ( x._2.toString, x._1 ) ) )
    val cache = Map[LambdaExpression, LambdaExpression]()

    override def convert_formula( e: HOLFormula ): HOLFormula = {
      //require(e.isInstanceOf[FOLFormula], "Expecting prover 9 formula "+e+" to be from the FOL layer, but it is not.")

      BetaReduction.betaNormalize(
        undoHol2Fol.backtranslate( e, sig_vars, sig_consts, absmap ) )
    }

    override def convert_substitution( s: Substitution ): Substitution = {
      val mapping = s.map.toList.map {
        case ( from, to ) =>
          (
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( from, sig_vars, sig_consts, absmap, None ) ).asInstanceOf[Var],
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( to, sig_vars, sig_consts, absmap, None ) ) )
      }

      Substitution( mapping )
    }
  }


 object Robinson2RalAndUndoHOL2Fol {
    def apply(sig_vars : Map[String, List[Var]],
              sig_consts : Map[String, List[Const]],
              cmap : replaceAbstractions.ConstantsMap) =
      new Robinson2RalAndUndoHOL2Fol(sig_vars, sig_consts, cmap)
  }

      show("Loading file")
      val pdb = HybridLatexParser(filename)

      show("Eliminating definitions, expanding tautological axioms")
      val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))

      show("Skolemizing")
      val selp = LKToLKsk(elp)

      show("Extracting struct")
      val struct = StructCreators.extract(selp, x => containsQuantifierOnLogicalLevel(x) || freeHOVariables(x).nonEmpty)

      show("Computing projections")
      val proj = Projections(selp, x => containsQuantifierOnLogicalLevel(x) || freeHOVariables(x).nonEmpty)

      show("Computing clause set")
      val cl = SimpleStandardClauseSet(struct)

      show("Exporting to prover 9")
      val (cmap, folcl_) = replaceAbstractions(cl.toList)
      val folcl = reduceHolToFol(folcl_)

      show("Refuting clause set")
      val Some(rp) = Prover9.getRobinsonProof(folcl.map(_.asInstanceOf[FOLClause]))

      show("Getting formulas")
      val proofformulas = selp.nodes.flatMap(_.asInstanceOf[LKProof].root.toHOLSequent.formulas  ).toList.distinct

      show("Extracting signature from "+proofformulas.size+ " formulas")
      val (sigc, sigv) = undoHol2Fol.getSignature( proofformulas )

      show("Converting to Ral")

      val myconverter = Robinson2RalAndUndoHOL2Fol(sigv.map(x => (x._1, x._2.toList)), sigc.map(x => (x._1, x._2.toList)), cmap)
      val ralp = myconverter(rp)
      show("Creating acnf")
      val (acnf, endclause) = ceres_omega(proj, ralp, sequentToLabelledSequent(selp.root), struct)
      show("Compute expansion tree")
      val et = LKskToExpansionProof(acnf)
      show(" End of script ")
