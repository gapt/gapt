/** 
 * Description: 
**/

package at.logic.integration_tests

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import scala.xml._

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.lkSpecs.beMultisetEqual
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.getCutAncestors

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

class TapeTest extends SpecificationWithJUnit {
  "The system" should {
    "parse correctly the tape proof" in {
      val proofs = (new XMLReader(new InputStreamReader(new GZIPInputStream(new FileInputStream("target" + separator + "test-classes" + separator + "tape-in.xml.gz")))) with XMLProofDatabaseParser).getProofs()
      val proof = proofs.first
      val cut_occs = getCutAncestors( proof )
      val s = StructCreators.extract( proof, cut_occs )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      def sequentToString( s: Sequent ) = {
        var ret = ""
        s.antecedent.foreach( formula => ret += formula.toStringSimple + ", ")
        ret += " :- "
        s.succedent.foreach( formula => ret += formula.toStringSimple + ", ")
        ret
      }
      cs.foreach( s => print( sequentToString( s ) + "\n") )
      proofs.size must beEqual(1)
    }
  }
}
