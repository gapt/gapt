
package gapt.integration_tests

import gapt.expr.{ Atom, Formula, Top }
import gapt.expr.hol.containsStrongQuantifier
import gapt.proofs.{ Ant, HOLClause, SequentConnector, Suc }
import gapt.proofs.expansion.ExpansionSequent
import gapt.formats.tptp.TPTPFOLExporter
import gapt.proofs.lk._
import gapt.provers.prover9._
import gapt.provers.verit.VeriT
import gapt.proofs.ceres.{ deleteTautologies, _ }
import gapt.examples.prime
import java.io.File.separator
import java.io.{ FileInputStream, FileReader, IOException, InputStreamReader }
import java.util.zip.GZIPInputStream

import gapt.provers.smtlib.Z3
import org.specs2.mutable._

//TODO: without elimination of schematic definitions (in the hlk sense), only the smallest instance works

class PrimeProofTest extends Specification {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

  "The system" should {
    //    "parse correctly the second-order prime proof" in {
    //      val pdb = (new XMLReader(new InputStreamReader(
    // new GZIPInputStream(getClass.getClassLoader.getResourceAsStream("prime2.xml.gz"))))
    // with XMLProofDatabaseParser).getProofDatabase()
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
    //      val seq1 = Sequent(Nil, Atom(ConstantStringSymbol("<"),
    // Const(ConstantStringSymbol("0"), Ti())::Function(ConstantStringSymbol("p"),
    // Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
    //      val seq2 = Sequent(Nil, Atom(ConstantStringSymbol("<"),
    // Const(ConstantStringSymbol("1"), Ti())::Function(ConstantStringSymbol("p"),
    // Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
    //      val seq3 = Sequent(Nil, Atom(ConstantStringSymbol("="),
    // Var(VariableStringSymbol("x"), Ti())::(Var(VariableStringSymbol("x"), Ti())::Nil))::Nil)
    //      val seq4 = Sequent(Nil, Atom(ConstantStringSymbol("="),
    // Function(ConstantStringSymbol("+"), Const(ConstantStringSymbol("0"), Ti())
    // ::Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Var(VariableStringSymbol("x"), Ti())::Nil)::Nil)
    //
    //      val holcs : List[Sequent] = pdb.axioms ::: List[Sequent](seq1,seq2,seq3,seq4) ::: csPre
    //
    //      // maps original types and definitions of abstractions
    //      val sectionsPre = ("Types", getTypeInformation(holcs).toList.sortWith((x,y) => x.toString < y.toString))
    // ::Nil
    //
    //      // convert to fol and obtain map of definitons
    //      val imap = Map[gapt.expr.typedLambdaCalculus.Expr,
    // gapt.language.hol.logicSymbols.ConstantStringSymbol]()
    //      val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
    //      val cs = holcs.map(x => Sequent(
    //          x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[Expr],imap,iid).asInstanceOf[FOLFormula]),
    //          x.succedent.map(y => reduceHolToFol(y.asInstanceOf[Expr],imap,iid).asInstanceOf[FOLFormula])
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
    //      val pb = new gapt.utils.ds.PublishingBuffer[Clause]
    //      pb.insertAll(0,cssv.map(x => at.logic.calculi.resolution.base.Clause(
    // x.antecedent.asInstanceOf[List[Formula]], x.succedent.asInstanceOf[List[Formula]])))
    //      val ref = new gapt.provers.atp.refinements.UnitRefinement(pb)
    //      val subsumMng = new gapt.proofs.lk.algorithms.subsumption.managers.SimpleManager(
    // pb.asInstanceOf[gapt.utils.ds.PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
    //        new gapt.proofs.lk.algorithms.subsumption.StillmanSubsumptionAlgorithm{
    // val matchAlg = gapt.algorithms.matching.fol.FOLMatchingAlgorithm})
    //        AutomatedFOLStream(-1, new gapt.provers.atp.refinements.UnitRefinement(pb), subsumMng)
    //      val res = new Prover{}.refute(AutomatedFOLStream(-1,
    // new gapt.provers.atp.refinements.UnitRefinement(pb), subsumMng))
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
    //      (new FileWriter("target" + separator + "prime2-cs-subsumed.tex") with SequentsListLatexExporter
    // with HOLTermArithmeticalExporter)
    //        .exportSequentList(subsum, sections).close
    //      (new FileWriter("target" + separator + "prime2-cs.tex") with SequentsListLatexExporter
    // with HOLTermArithmeticalExporter)
    //        .exportSequentList(neg.sortWith(mySort) ++ mix.sortWith(mySort) ++ pos.sortWith(mySort), sections).close
    // /*     (new FileWriter("target" + separator + "prime2-cs-unit.tex") with SequentsListLatexExporter
    // with HOLTermArithmeticalExporter)
    //        .exportSequentList(neg2.sort(mySort) ++ mix2.sort(mySort) ++ pos2.sort(mySort), sections).close*/
    //      //saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::
    // Tuple2("cssv", cssv.toList)::Nil, "target" + separator + "prime2-cs.xml" )
    //      //saveXML( Tuple2("cs", cs)::Tuple2("dcs", dcs)::Tuple2("css", (css.toList))::
    // Tuple2("cssv", cssv.toList)::Nil, "target" + separator + "prime2-cs.xml" )
    //    }

    def prime1( n: Int, refute: Boolean ) = {
      skipped( "higher-order definition elimination fails & prover9 does not understand many-sorted logic" )
      checkForProverOrSkip
      if ( !Z3.isInstalled ) skipped

      val primeN = prime.furstenberg( n )
      val proof = primeN.proof

      if ( false ) {
        if ( VeriT.isInstalled ) {
          // test expansion tree extraction by verifying that the deep formula is a tautology
          // can't extract ETs in the presence of definitions currently
          val definitionFreeProof = eliminateDefinitions( primeN.ctx.definitions.toMap )( proof )
          val etSeq = LKToExpansionProof( definitionFreeProof )
          val fSequent = etSeq.deep
          VeriT.isValid( fSequent ) must beTrue
        }
      }

      //      val deproof = DefinitionElimination( proofdb.Definitions )( proof )
      val proof_sk = folSkolemize( regularize( AtomicExpansion( proof ) ) )
      println( "es: " + proof_sk.endSequent + " " + containsStrongQuantifier( proof_sk.endSequent ) )
      val s = extractStruct( proof_sk, CERES.skipEquations )

      val cs = deleteTautologies( CharacteristicClauseSet( s ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs.toList )
      //      val writer = new java.io.FileWriter( "target" + separator + "prime1-" + n + "-cs.tptp" )
      //      writer.write( tptp.toString )
      //      writer.flush
      val projs = Projections( proof_sk, CERES.skipEquations )
      val path = "target" + separator + "prime1-" + n + "-sk.xml"

      if ( refute ) {
        Prover9.getResolutionProof( cs ) match {
          case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
          case Some( _ ) => true must beEqualTo( true )
        }
      }

      ok
    }

    def euclid( n: Int ) = {
      if ( n >= 2 ) skipped( "LK proof construction runs out of memory" )

      val euclidN = prime.euclid( n )
      import euclidN._

      CERES( eliminateDefinitions( proof ) )
      ok
    }

    "euclid 0" in euclid( 0 )
    "euclid 1" in euclid( 1 )
    "euclid 2" in euclid( 2 )

    "prime1 0 with refutation" in prime1( 0, true )
    "prime1 1" in prime1( 1, false )
    "prime1 2" in prime1( 2, false )
  }
}
