
package at.logic.integration_tests

import at.logic.algorithms.fol.hol2fol._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.eliminateDefinitions
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.subsumption._
import at.logic.calculi.expansionTrees.{toDeep, ExpansionSequent}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.language.fol.FOLFormula
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.parsing.calculi.latex.SequentsListLatexExporter
import at.logic.parsing.calculus.xml.saveXML
import at.logic.parsing.language.arithmetic.HOLTermArithmeticalExporter
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.parsing.writers.FileWriter
import at.logic.provers.prover9._
import at.logic.provers.veriT.VeriTProver
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.transformations.ceres.clauseSets.profile._
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.{StructCreators, structToExpressionTree}
import at.logic.transformations.herbrandExtraction.extractExpansionSequent
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.transformations.skolemization.skolemize


/* comment out until atp works again
import at.logic.provers.atp.Prover
import at.logic.provers.atp.commands._
import at.logic.provers.atp.refinements.UnitRefinement
*/

import java.io.File.separator
import java.io.{IOException, FileReader, FileInputStream, InputStreamReader}
import java.util.zip.GZIPInputStream
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class PrimeProofTest extends SpecificationWithJUnit {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toString + ", ")
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toString + ", ")
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print("unary: " + stats.unary + "\n")
    print("binary: " + stats.binary + "\n")
    print("cuts: " + stats.cuts + "\n")
  }

  def mySort(x: Sequent, y: Sequent) = (x.toString < y.toString) // lexicographically

  "The system" should {
//    "parse correctly the second-order prime proof" in {
//      val pdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("prime2.xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
//      pdb.proofs.size must beEqualTo(1)
//      val proof = pdb.proofs.head
//      printStats( proof )
//
//      val proof_sk = LKtoLKskc( proof )
//      val s = StructCreators.extract( proof_sk )
//
//      val csPre : List[Sequent] = StandardClauseSet.transformStructToClauseSet(s) map (_.getSequent)
//
//      // we will add three axioms: 0 < p(x), 1 < p(x), x = x
//      val seq1 = Sequent(Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("0"), Ti())::Function(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
//      val seq2 = Sequent(Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Function(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
//      val seq3 = Sequent(Nil, Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLVar(VariableStringSymbol("x"), Ti())::Nil))::Nil)
//      val seq4 = Sequent(Nil, Atom(ConstantStringSymbol("="), Function(ConstantStringSymbol("+"), HOLConst(ConstantStringSymbol("0"), Ti())::HOLVar(VariableStringSymbol("x"), Ti())::Nil, Ti())::HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)
//
//      val holcs : List[Sequent] = pdb.axioms ::: List[Sequent](seq1,seq2,seq3,seq4) ::: csPre
//
//      // maps original types and definitions of abstractions
//      val sectionsPre = ("Types", getTypeInformation(holcs).toList.sortWith((x,y) => x.toString < y.toString))::Nil
//
//      // convert to fol and obtain map of definitons
//      val imap = Map[at.logic.language.lambda.typedLambdaCalculus.LambdaExpression, at.logic.language.hol.logicSymbols.ConstantStringSymbol]()
//      val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
//      val cs = holcs.map(x => Sequent(
//          x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula]),
//          x.succedent.map(y => reduceHolToFol(y.asInstanceOf[HOLExpression],imap,iid).asInstanceOf[FOLFormula])
//      ))
//      val sections = ("Definitions", imap.toList.map(x => (x._1, FOLConst(x._2))))::sectionsPre
//
//      val dcs = deleteTautologies( cs )
//      Console.println("dcs size: " + dcs.size)
//      val css = dcs.distinct
//      Console.println("css size: " + css.size)
//
//      val cssUnit = simpleUnitResolutionNormalization(css)
//      Console.println("cssUnit size: " + cssUnit.size)
//
//      val scss = subsumedClausesRemoval(cssUnit)
//      Console.println("scss size: " + scss.size)
//
//      val cssv = sequentNormalize(scss)
//      Console.println("cssv size: " + cssv.size)
//
// /*     // apply unit resolution and subsumption on the resulted clause set
//      val pb = new at.logic.utils.ds.PublishingBuffer[Clause]
//      pb.insertAll(0,cssv.map(x => at.logic.calculi.resolution.base.Clause(x.antecedent.asInstanceOf[List[HOLFormula]], x.succedent.asInstanceOf[List[HOLFormula]])))
//      val ref = new at.logic.provers.atp.refinements.UnitRefinement(pb)
//      val subsumMng = new at.logic.algorithms.subsumption.managers.SimpleManager(pb.asInstanceOf[at.logic.utils.ds.PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
//        new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm{val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm})
//        AutomatedFOLStream(-1, new at.logic.provers.atp.refinements.UnitRefinement(pb), subsumMng)
//      val res = new Prover{}.refute(AutomatedFOLStream(-1, new at.logic.provers.atp.refinements.UnitRefinement(pb), subsumMng))
//      Console.println("has a refutation? " + (!res.isEmpty))
//      val newUnitSet = pb.toList
//      Console.println("newUnitSet size: " + newUnitSet.size)
//      val newUnitSetSubsum = subsumedClausesRemoval(newUnitSet)
//      Console.println("newUnitSetSubsum size: " + newUnitSetSubsum.size)
//*/
//      // done for preserving order
//      val neg = cssv.filter(x => x.succedent.isEmpty)
//      val mix = cssv.filter(x => !x.succedent.isEmpty && !x.antecedent.isEmpty)
//      val pos = cssv.filter(x => x.antecedent.isEmpty)
///*
//      // done for preserving order
//      val neg2 = newUnitSetSubsum.filter(x => x.succedent.isEmpty)
//      val mix2 = newUnitSetSubsum.filter(x => !x.succedent.isEmpty && !x.antecedent.isEmpty)
//      val pos2 = newUnitSetSubsum.filter(x => x.antecedent.isEmpty)
//*/
//      val subsum = sequentNormalize(cssUnit).diff(cssv)
//      Console.println("subsum size: " + subsum.size)
//      (new FileWriter("target" + separator + "prime2-cs-subsumed.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
//        .exportSequentList(subsum, sections).close
//      (new FileWriter("target" + separator + "prime2-cs.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
//        .exportSequentList(neg.sortWith(mySort) ++ mix.sortWith(mySort) ++ pos.sortWith(mySort), sections).close
// /*     (new FileWriter("target" + separator + "prime2-cs-unit.tex") with SequentsListLatexExporter with HOLTermArithmeticalExporter)
//        .exportSequentList(neg2.sort(mySort) ++ mix2.sort(mySort) ++ pos2.sort(mySort), sections).close*/
//      //saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::Tuple2("cssv", cssv.toList)::Nil, "target" + separator + "prime2-cs.xml" )
//      //saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::Tuple2("cssv", cssv.toList)::Nil, "target" + separator + "prime2-cs.xml" )
//    }


    def prime1(n: Int, refute: Boolean) = {
      checkForProverOrSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("prime1-" + n + ".xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2

      val veriT = new VeriTProver()

      if (false) { // run this code as soon as issue 260 is fixed:
        if (veriT.isInstalled()) {
          // test expansion tree extraction by verifying that the deep formula is a tautology
          val definitionFreeProof = eliminateDefinitions(proof) // can't extract ETs in the presence of definitions currently
          val etSeq = extractExpansionSequent(definitionFreeProof, false)
          val fSequent = toDeep(etSeq)
          veriT.isValid(fSequent) must beTrue
        }
      }

      //val proof_sk = skolemize( regularize( proof )._1 )
      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      // convert struct DAG to tree
      structToExpressionTree( s )

      val prf = deleteTautologies(proofProfile(s, proof_sk) map (_.toFSequent))

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter("target" + separator + "prime1-" + n + "-prf.tptp")
      writer_prf.write( tptp_prf )
      writer_prf.flush



      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "prime1-" + n + "-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "prime1-" + n + "-sk.xml"

      val prf_cs_intersect = prf.filter(seq => cs.contains(seq))

      if (refute) {
        Prover9.refute( prf ) match {
          case None => "" must beEqualTo("refutation of proof profile failed")
          case Some(_) => true must beEqualTo(true)
        }
        Prover9.refute( cs ) match {
          case None => "" must beEqualTo("refutation of struct cs in tptp format failed")
          case Some(_) => true must beEqualTo(true)
        }
      }

      saveXML( Tuple2("prime1-" + n + "-sk", proof_sk) ::
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2("cs", cs)::Tuple2("prf",prf)::Tuple2("cs_prf_intersection", prf_cs_intersect)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqualTo( true )
    }


    def euclid(n: Int) = {
      checkForProverOrSkip

      val proofdb = (new XMLReader(new InputStreamReader(new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("euclid-" + n + ".xml.gz")))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2

      //val proof_sk = skolemize( regularize( proof )._1 )
      val proof_sk = skolemize( proof )
      val s = StructCreators.extract( proof_sk )

      // convert struct DAG to tree
      structToExpressionTree( s )

      val prf = deleteTautologies(proofProfile(s, proof_sk).map( _.toFSequent ))

      val tptp_prf = TPTPFOLExporter.tptp_problem( prf )
      val writer_prf = new java.io.FileWriter("target" + separator + "euclid-" + n + "-prf.tptp")
      writer_prf.write( tptp_prf )
      writer_prf.flush



      val cs = deleteTautologies( StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs )
      val writer = new java.io.FileWriter("target" + separator + "euclid-" + n + "-cs.tptp")
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk )
      val path = "target" + separator + "euclid-" + n + "-sk.xml"

      val prf_cs_intersect = prf.filter(seq => cs.contains(seq))


      //Prover9.refute( cs ) must beEqualTo( true )
      //Prover9.refute( prf ) must beEqualTo( true )

      saveXML( Tuple2("euclid-" + n + "-sk", proof_sk) ::
        projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        Tuple2("cs", cs)::Tuple2("prf",prf)::Tuple2("cs_prf_intersection", prf_cs_intersect)::Nil, path )
      (new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=0" in euclid(0)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=1" in euclid(1)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=2" in euclid(2)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=0" in prime1(0, true)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=1" in prime1(1, false)

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=2" in prime1(2, false)
     }
}
