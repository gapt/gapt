package at.logic.gapt.proofs.ceres_schema.ACNF

import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.applySubstitution
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lk.lkNew2Old
import at.logic.gapt.proofs.occurrences.{ FormulaOccurrence, defaultFormulaOccurrenceFactory }
import at.logic.gapt.proofs.resolution.RobinsonToLK
import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.formats.shlk_parsing.sFOParser
import at.logic.gapt.proofs.ceres_schema.clauseSchema._
import at.logic.gapt.proofs.ceres_schema.clauseSets.StandardClauseSet
import at.logic.gapt.proofs.ceres_schema.projections.Projections
import at.logic.gapt.proofs.ceres_schema.struct.StructCreators
import java.io.{ FileInputStream, InputStreamReader }
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable._

class acnfTest extends Specification {
  implicit val factory = defaultFormulaOccurrenceFactory

  args( sequential = true )
  "ACNFTest" should {
    "should create correctly the ACNF for journal_example.lks" in {
      skipped( "Error at: at.logic.gapt.proofs.algorithms.ceres.clauseSchema.ResDeductionToLKTree$.apply(clauseSchema.scala:659)" )

      val s1 = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "ceres-journal_example.lks" ) )
      val s2 = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "resSchema1.rs" ) )
      val map = sFOParser.parseProof( s1 )
      ParseResSchema( s2 )
      val p = ACNF( "\\varphi", "\\rho_1", 2 )
      ok
    }

    //TODO: fix it ! The problem is that it needs cloning before plugging in a projection into the skeleton resolution proof.
    //
    //    "should create correctly the ACNF for journal_example.lks" in {
    //      val dnLine = sys.props( "line.separator" ) + sys.props("line.separator")
    //      //println(Console.BLUE+ dnLine + dnLine + "------- ACNF for the journal example instance = 0 ------- " + dnLine +Console.RESET)
    //      val s1 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("ceres-journal_example.lks"))
    //      val s2 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema1.rs"))
    //      val map = sFOParser.parseProof(s1)
    //      ParseResSchema(s2)
    //      val p = ACNF("\\varphi", "\\rho_1", 0)
    ////      printSchemaProof(p)
    //      //println( dnLine + "--- END ---" + dnLine )
    //      ok
    //    }

    "should create correctly the ACNF for sEXP.lks" in {
      skipped( "Error at: at.logic.gapt.proofs.algorithms.ceres.clauseSchema.ResDeductionToLKTree$.apply(clauseSchema.scala:659)" )

      val s1 = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "sEXP.lks" ) )
      val s2 = new InputStreamReader( getClass.getClassLoader.getResourceAsStream( "resSchema_sEXP.rs" ) )
      val map = sFOParser.parseProof( s1 )
      ParseResSchema( s2 )
      val p = ACNF( "\\psi", "\\rho_1", 1 )
      ok
    }

    "should correctly handle equality rules" in {
      def groundproj( projections: Set[LKProof], groundSubs: List[( Var, LambdaExpression )] ): Set[LKProof] = {
        groundSubs.map( subs => projections.map( pr => renameIndexedVarInProjection( pr, subs ) ) ).flatten.toSet
      }

      val List( uv, fuu, fuv, ab, fab ) = List( "u = v", "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)" ) map ( Prover9TermParserLadrStyle.parseFormula )
      val List( uy, xy, ay ) = List(
        "(all y (u = y -> f(u) = f(y)))",
        "(all x all y (x = y -> f(x) = f(y)))",
        "(all y (a = y -> f(a) = f(y)))"
      ) map ( Prover9TermParserLadrStyle.parseFormula )
      val List( u, v ) = List( "u", "v" ).map( s => FOLVar( s ) )
      val List( a, b ) = List( "a", "b" ).map( s => FOLConst( s ) )
      val ax1 = Axiom( List( uv ), List( uv ) )
      val ax2 = Axiom( List(), List( fuu ) )
      val ax3 = Axiom( List( ab ), List( ab ) )
      val ax4 = Axiom( List( fab ), List( fab ) )

      val i1 = EquationRight1Rule( ax1, ax2, ax1.root.succedent( 0 ), ax2.root.succedent( 0 ), fuv )
      val i2 = ImpRightRule( i1, i1.root.antecedent( 0 ), i1.root.succedent( 0 ) )
      val i3 = ForallRightRule( i2, i2.root.succedent( 0 ), uy, v )
      val i4 = ForallRightRule( i3, i3.root.succedent( 0 ), xy, u )

      val i5 = ImpLeftRule( ax3, ax4, ax3.root.succedent( 0 ), ax4.root.antecedent( 0 ) )
      val i6 = ForallLeftRule( i5, i5.root.antecedent( 1 ), ay, b )
      val i7 = ForallLeftRule( i6, i6.root.antecedent( 1 ), xy, a )

      val es = CutRule( i4, i7, i4.root.succedent( 0 ), i7.root.antecedent( 1 ) )

      val cs = StandardClauseSet.transformStructToClauseSet( StructCreators.extract( es ) )

      val rp = Escargot.getRobinsonProof( cs.toList.map( _.toHOLSequent.asInstanceOf[HOLClause] ) )
      rp must not beEmpty

      val proj = Projections( es )
      proj must not beEmpty

      //for (p <- proj) println(p)
      val rlkp = RobinsonToLK( rp.get )
      val gproj = proj map ( applySubstitution( _, FOLSubstitution( u -> a, v -> a ) )._1 )
      //gproj map (x => println(" "+x))
      val acnf = ACNF.plugProjections( lkNew2Old( rlkp ), gproj, es.root.toHOLSequent )
      //println(acnf)

      true must beEqualTo( true )
    }
  }
}

