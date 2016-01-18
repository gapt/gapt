
package at.logic.gapt.integration_tests

import at.logic.gapt.expr.Top
import at.logic.gapt.expr.hol.containsStrongQuantifier
import at.logic.gapt.formats.xml.{ XMLParser, saveXML }
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.proofs.expansion.{ toDeep, ExpansionSequent }
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import XMLParser._
import at.logic.gapt.formats.readers.XMLReaders._
import at.logic.gapt.formats.writers.FileWriter
import at.logic.gapt.proofs.lkOld.deleteTautologies
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.prover9._
import at.logic.gapt.provers.veriT.VeriT
import at.logic.gapt.proofs.ceres._

import java.io.File.separator
import java.io.{ IOException, FileReader, FileInputStream, InputStreamReader }
import java.util.zip.GZIPInputStream
import org.specs2.mutable._

//TODO: without elimination of schematic definitions (in the hlk sense), only the smallest instance works

class PrimeProofTest extends Specification {
  def checkForProverOrSkip = Prover9.isInstalled must beTrue.orSkip

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
    //      val seq1 = Sequent(Nil, Atom(ConstantStringSymbol("<"), Const(ConstantStringSymbol("0"), Ti())::Function(ConstantStringSymbol("p"), Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
    //      val seq2 = Sequent(Nil, Atom(ConstantStringSymbol("<"), Const(ConstantStringSymbol("1"), Ti())::Function(ConstantStringSymbol("p"), Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Nil)::Nil)
    //      val seq3 = Sequent(Nil, Atom(ConstantStringSymbol("="), Var(VariableStringSymbol("x"), Ti())::(Var(VariableStringSymbol("x"), Ti())::Nil))::Nil)
    //      val seq4 = Sequent(Nil, Atom(ConstantStringSymbol("="), Function(ConstantStringSymbol("+"), Const(ConstantStringSymbol("0"), Ti())::Var(VariableStringSymbol("x"), Ti())::Nil, Ti())::Var(VariableStringSymbol("x"), Ti())::Nil)::Nil)
    //
    //      val holcs : List[Sequent] = pdb.axioms ::: List[Sequent](seq1,seq2,seq3,seq4) ::: csPre
    //
    //      // maps original types and definitions of abstractions
    //      val sectionsPre = ("Types", getTypeInformation(holcs).toList.sortWith((x,y) => x.toString < y.toString))::Nil
    //
    //      // convert to fol and obtain map of definitons
    //      val imap = Map[at.logic.gapt.expr.typedLambdaCalculus.LambdaExpression, at.logic.gapt.language.hol.logicSymbols.ConstantStringSymbol]()
    //      val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
    //      val cs = holcs.map(x => Sequent(
    //          x.antecedent.map(y => reduceHolToFol(y.asInstanceOf[LambdaExpression],imap,iid).asInstanceOf[FOLFormula]),
    //          x.succedent.map(y => reduceHolToFol(y.asInstanceOf[LambdaExpression],imap,iid).asInstanceOf[FOLFormula])
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
    //      val pb = new at.logic.gapt.utils.ds.PublishingBuffer[Clause]
    //      pb.insertAll(0,cssv.map(x => at.logic.calculi.resolution.base.Clause(x.antecedent.asInstanceOf[List[Formula]], x.succedent.asInstanceOf[List[Formula]])))
    //      val ref = new at.logic.gapt.provers.atp.refinements.UnitRefinement(pb)
    //      val subsumMng = new at.logic.gapt.proofs.lk.algorithms.subsumption.managers.SimpleManager(pb.asInstanceOf[at.logic.gapt.utils.ds.PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
    //        new at.logic.gapt.proofs.lk.algorithms.subsumption.StillmanSubsumptionAlgorithm{val matchAlg = at.logic.gapt.algorithms.matching.fol.FOLMatchingAlgorithm})
    //        AutomatedFOLStream(-1, new at.logic.gapt.provers.atp.refinements.UnitRefinement(pb), subsumMng)
    //      val res = new Prover{}.refute(AutomatedFOLStream(-1, new at.logic.gapt.provers.atp.refinements.UnitRefinement(pb), subsumMng))
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

    def prime1( n: Int, refute: Boolean ) = {
      skipped( "Does not work right now - without definition elimination the end-sequent looks skolemized but it isn't." )
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "prime1-" + n + ".xml.gz" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2

      if ( false ) { // run this code as soon as issue 260 is fixed:
        if ( VeriT.isInstalled ) {
          // test expansion tree extraction by verifying that the deep formula is a tautology
          val definitionFreeProof = DefinitionElimination( proofdb.Definitions )( proof ) // can't extract ETs in the presence of definitions currently
          val etSeq = LKToExpansionProof( definitionFreeProof )
          val fSequent = toDeep( etSeq )
          VeriT.isValid( fSequent ) must beTrue
        }
      }

      //      val deproof = DefinitionElimination( proofdb.Definitions )( proof )
      val proof_sk = skolemize( regularize( AtomicExpansion( proof ) ) )
      println( "es: " + proof_sk.endSequent + " " + containsStrongQuantifier( proof_sk.endSequent ) )
      val s = extractStruct( proof_sk, CERES.skipEquations )

      val cs = deleteTautologies( CharacteristicClauseSet( s ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs.toList )
      val writer = new java.io.FileWriter( "target" + separator + "prime1-" + n + "-cs.tptp" )
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk, CERES.skipEquations )
      val path = "target" + separator + "prime1-" + n + "-sk.xml"

      if ( refute ) {
        Prover9.getRobinsonProof( cs ) match {
          case None      => "" must beEqualTo( "refutation of struct cs in tptp format failed" )
          case Some( _ ) => true must beEqualTo( true )
        }
      }

      saveXML(
        Tuple2( "prime1-" + n + "-sk", lkNew2Old( proof_sk ) ) ::
          projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", lkNew2Old( p._1 ) ) ),
        //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", p._1 ) ),
        ( "cs", cs.toList ) :: Nil, path
      )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    def euclid( n: Int ) = {
      skipped( "Does not work right now - without definition elimination the end-sequent looks skolemized but it isn't." )
      checkForProverOrSkip

      val proofdb = ( new XMLReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "euclid-" + n + ".xml.gz" ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
      proofdb.proofs.size must beEqualTo( 1 )
      val proof = proofdb.proofs.head._2
      //      val deproof = DefinitionElimination( proofdb.Definitions )( proof )

      val proof_sk = skolemize( regularize( AtomicExpansion( proof ) ) )
      val s = extractStruct( proof_sk, CERES.skipEquations )

      val cs = deleteTautologies( CharacteristicClauseSet( s ) )
      val tptp = TPTPFOLExporter.tptp_problem( cs.toList )
      val writer = new java.io.FileWriter( "target" + separator + "euclid-" + n + "-cs.tptp" )
      writer.write( tptp )
      writer.flush
      val projs = Projections( proof_sk, CERES.skipEquations )
      val path = "target" + separator + "euclid-" + n + "-sk.xml"

      //new Prover9Prover().getRobinsonProof( cs ) must beEqualTo( true )
      saveXML(
        Tuple2( "euclid-" + n + "-sk", lkNew2Old( proof_sk ) ) ::
          projs.toList.zipWithIndex.map( p => Tuple2( "\\psi_{" + p._2 + "}", lkNew2Old( p._1 ) ) ),
        Tuple2( "cs", cs.toList ) :: Nil, path
      )
      ( new java.io.File( path ) ).exists() must beEqualTo( true )
    }

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=0" in euclid( 0 )

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=1" in euclid( 1 )

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof (Euclid's proof), n=2" in euclid( 2 )

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=0" in prime1( 0, true )

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=1" in prime1( 1, false )

    "parse, skolemize, and export the clause set in TPTP of the first-order prime proof, n=2" in prime1( 2, false )
  }
}
