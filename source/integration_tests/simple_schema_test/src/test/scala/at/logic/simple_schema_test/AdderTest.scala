package at.logic.simple_schema_test

import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.parsing.writers.FileWriter
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.algorithms.shlk._
import io.Source
import java.io.File.separator
import at.logic.language.schema.IntVar
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.Sequent
import at.logic.utils.ds.Multisets.HashMultiset
import at.logic.language.schema.{IndexedPredicate, SchemaFormula}
import at.logic.transformations.ceres.struct.{ClauseSetSymbol, StructCreators}
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.language.hol.HOLFormula

@RunWith(classOf[JUnitRunner])
class AdderTest extends SpecificationWithJUnit {

  "AdderTest" should {

   "extract a schema clause set from an Adder proof" in {

      SHLK.parseProofs(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "adder.lks")))

      val n = IntVar(new VariableStringSymbol("n"))

      val s = StructCreators.extractStruct( "\\psi", n)
      val ccs : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s)

//      val m_empty = HashMultiset[HOLFormula]()
//      var cc: at.logic.transformations.ceres.struct.TypeSynonyms.CutConfiguration = (m_empty, m_empty)
//
//      val cs_pruned_psi = cs.filter( s => s.antecedent.isEmpty || s.antecedent.exists( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol => sym.cut_occs == cc && sym.name == "psi"
//        case _ => false
//      }
//      case _ => false
//    } ) )
//
//      cs_pruned_psi.foreach( s => s.succedent.foreach( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol if sym.name == "varphi" => cc = sym.cut_occs
//        case _ => false
//      }
//      case _ => false
//    } ))
//
//      val cs_pruned_varphi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol => sym.cut_occs == cc
//        case _ => false
//      }
//      case _ => false
//    } ) )
//
//       cs_pruned_varphi.foreach( s => s.succedent.foreach( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol if sym.name == "phi" => cc = sym.cut_occs
//        case _ => false
//      }
//      case _ => false
//    } ))
//
//       val cs_pruned_phi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol => sym.cut_occs == cc
//        case _ => false
//      }
//      case _ => false
//    } ) )
//
//      cs_pruned_psi.foreach( s => s.succedent.foreach( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol if sym.name == "chi" => cc = sym.cut_occs
//        case _ => false
//      }
//      case _ => false
//    } ))
//
//      val cs_pruned_chi = cs.filter( s => s.antecedent.exists( fo => fo.formula match {
//      case IndexedPredicate(pred, _) => pred.name match {
//        case sym : ClauseSetSymbol => sym.cut_occs == cc
//        case _ => false
//      }
//      case _ => false
//    } ) )
//
//      val ccs = cs_pruned_psi ::: cs_pruned_varphi ::: cs_pruned_phi ::: cs_pruned_chi

      (new FileWriter("target" + separator + "test-classes" + separator + "ccs_pruned.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter).exportSequentList(ccs.map(_.toFSequent), Nil).close
      // specs2 require a least one Result, see org.specs2.specification.Example
      Success()
    }//.pendingUntilFixed("needs too much memory to pass")
  }
}
