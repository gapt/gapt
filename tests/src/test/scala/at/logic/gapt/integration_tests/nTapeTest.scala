package at.logic.gapt.integration_tests

import at.logic.gapt.examples.nTape
import at.logic.gapt.formats.llkNew.loadLLK
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lkskNew.LKskProof
import at.logic.gapt.proofs.lkskNew.LKskProof.Label
import at.logic.gapt.provers.prover9.Prover9

import org.specs2.mutable._

class nTapeTest extends Specification {
  /*
  def show( s: String ) = Unit //println( "+++++++++ " + s + " ++++++++++" )
  def show_detail( s: String ) = Unit //println( "+++++++++ " + s + " ++++++++++" )

  def f( e: LambdaExpression ): String = toLLKString( e )

  case class Robinson2RalAndUndoHOL2Fol(
      sig_vars:   Map[String, List[Var]],
      sig_consts: Map[String, List[Const]],
      cmap:       replaceAbstractions.ConstantsMap
  ) extends RobinsonToRal {
    val absmap = Map[String, LambdaExpression]() ++ ( cmap.toList.map( x => ( x._2.toString, x._1 ) ) )

    override def convert_formula( e: HOLFormula ): HOLFormula = {
      BetaReduction.betaNormalize(
        undoHol2Fol.backtranslate( e, sig_vars, sig_consts, absmap )
      )
    }

    override def convert_substitution( s: Substitution ): Substitution = {
      val mapping = s.map.toList.map {
        case ( from, to ) =>
          (
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( from, sig_vars, sig_consts, absmap, None ) ).asInstanceOf[Var],
            BetaReduction.betaNormalize( undoHol2Fol.backtranslate( to, sig_vars, sig_consts, absmap, None ) )
          )
      }

      Substitution( mapping )
    }
  }


  def decompose( et: ExpansionTree ): List[ExpansionTree] = et match {
    case ETAnd( x, y ) => decompose( x ) ++ decompose( y );
    case _             => List( et )
  }

  //prints the interesting terms from the expansion sequent
  def printStatistics( et: ExpansionSequent ) = {
    val conjuncts = decompose( et.antecedent( 1 ) )
    // FIXME: use a less fragile method to find the induction formula...
    val indet = conjuncts( 19 )
    val List( ind1, ind2 ): List[ExpansionTree] = indet match {
      case ETWeakQuantifier( _, SortedMap(
        ( et1, inst1 ),
        ( et2, inst2 )
        ) ) =>
        List( inst1, inst2 )
    }

    val ( ind1base, ind1step ) = ind1 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, SortedMap( ( base, _ ) ) ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, SortedMap( ( step, inst ) ) ) )
          )
        ), _ ) =>
        ( base, step )
    }

    val ( ind2base, ind2step ) = ind2 match {
      case ETImp( ETAnd(
        ETWeakQuantifier( _, SortedMap( ( base, _ ) ) ),
        ETSkolemQuantifier( _, _,
          ETImp( _, ETWeakQuantifier( f, SortedMap( ( step, inst ) ) ) )
          ) ), _ ) =>
        ( base, step )
    }

    ( ind1base, ind1step, ind2base, ind2step ) match {
      case ( Abs( xb, sb ), Abs( xs, ss ), Abs( yb, tb ), Abs( ys, ts ) ) =>
        val map = Map[LambdaExpression, StringSymbol]()
        val counter = new { private var state = 0; def nextId = { state = state + 1; state } }

        val ( map1, sb1 ) = replaceAbstractions( sb, map, counter )
        val ( map2, ss1 ) = replaceAbstractions( ss, map1, counter )
        val ( map3, tb1 ) = replaceAbstractions( tb, map2, counter )
        val ( map4, ts1 ) = replaceAbstractions( ts, map3, counter )

        show_detail( "base 1 simplified: " + f( Abs( xb, sb1 ) ) )
        show_detail( "base 2 simplified: " + f( Abs( yb, tb1 ) ) )
        show_detail( "step 1 simplified: " + f( Abs( xs, ss1 ) ) )
        show_detail( "step 2 simplified: " + f( Abs( ys, ts1 ) ) )

        show_detail( "With shortcuts:" )
        for ( ( term, sym ) <- map4 ) {
          show_detail( "Symbol: " + sym )
          show_detail( "Term:   " + f( term ) )
        }
    }

  }

  /**
   * The actual cut-elimination procedure.
   *
   * @param filename
   * @return Some(errormessage) if something breaks, None otherwise
   */
  def doCutelim( filename: String ): Option[String] = {
    show( "Loading file" )
    val pdb = loadLLK( getClass.getClassLoader getResourceAsStream filename )
    show( "Eliminating definitions, expanding tautological axioms" )
    val elp = AtomicExpansion( DefinitionElimination( pdb.Definitions )( regularize( pdb proof "TAPEPROOF" ) ) )
    show( "Skolemizing" )
    val selp = LKToLKsk( elp )

    show( "Extracting struct" )
    val struct = extractStructFromLKsk( selp, ceres_omega.skip_propositional )
    show( "Computing projections" )
    val proj = Projections( selp, ceres_omega.skip_propositional )

    show( "Computing clause set" )
    val cl = StandardClauseSet( struct )
    val cl_nolabels = cl.map( _.map( _._2 ) ).toList
    show( "Exporting to prover 9" )
    val ( cmap, folcl_ ) = replaceAbstractions( cl_nolabels )
    show_detail( "Calculated cmap: " )
    cmap.map( x => show_detail( x._1 + " := " + x._2 ) )

    val folcl = reduceHolToFol( folcl_ ).asInstanceOf[List[HOLClause]]
    folcl.map( x => show_detail( x.toString ) )

    show( "Refuting clause set" )
    Prover9.getRobinsonProof( folcl ) match {
      case None =>
        Some( "could not refute clause set" )
      case Some( rp ) =>
        show( "Getting formulas" )
        val proofformulas = for ( p <- selp.subProofs; f <- p.formulas.elements ) yield f

        show( "Extracting signature from " + proofformulas.size + " formulas" )
        val ( sigc, sigv ) = undoHol2Fol.getSignature( proofformulas.toList )

        show( "Converting to Ral" )

        val myconverter = Robinson2RalAndUndoHOL2Fol(
          sigv.map( x => ( x._1, x._2.toList ) ),
          sigc.map( x => ( x._1, x._2.toList ) ), cmap
        )
        val ralp = myconverter( rp )
        show( "Creating acnf" )
        val ( acnf, endclause ) = ceres_omega( proj, ralp, selp.conclusion, struct )

        show( "Compute expansion tree" )
        //TODO: fix
        //val et = LKskToExpansionProof( acnf )
        show( " HOORAY! " )

        //printStatistics( et )

        None
    }

  }
*/
  object nTape2Test extends nTape {
    override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "tape3.llk" )
    override def root_proof() = "TAPEPROOF"
  }

  object nTape3Test extends nTape {
    override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "tape3ex.llk" )
    override def root_proof() = "TAPEPROOF"
  }

  args( skipAll = !Prover9.isInstalled )
  "The higher-order tape proof" should {
    "do cut-elimination on the 2 copies tape proof (tape3.llk)" in {
      val acnf_labels = nTape2Test.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape2Test.acnf.conclusion.map( _._2 ) //discard labels
      println( nTape2Test.postprocessed_lkproof.conclusion )
      println( acnf_lkconclusion )
      acnf_lkconclusion.multiSetEquals( nTape2Test.postprocessed_lkproof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

    "do cut-elimination on the 1 copy tape proof (tape3ex.llk)" in {
      //skipped( "fails because projections add too much end-sequent material" )
      val acnf_labels = nTape3Test.acnf.conclusion.map( _._1 ).filter( _ != LKskProof.emptyLabel )
      acnf_labels must_== Sequent[Label]()

      val acnf_lkconclusion = nTape3Test.acnf.conclusion.map( _._2 )
      acnf_lkconclusion.multiSetEquals( nTape3Test.postprocessed_lkproof.conclusion ) must beTrue

      ok( "acnf could be created" )
    }

  }

}
