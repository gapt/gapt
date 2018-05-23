package gapt.testing
import cats.Later
import gapt.examples.tip._
import gapt.expr._
import gapt.proofs.expansion._
import gapt.proofs.lk._
import gapt.provers.viper.grammars.{ TreeGrammarProver, TreeGrammarProverOptions, indElimReversal }
import gapt.utils.verbose

object sipReconstruct extends scala.App {

  val indProofs =
    Map(
      "isaplanner.prop_03.1" -> Later( isaplanner.prop_03.ctx -> isaplanner.prop_03.proof ),
      "isaplanner.prop_03.2" -> Later( isaplanner.prop_03.ctx -> isaplanner.prop_03.proof2 ),
      "isaplanner.prop_03.3" -> Later( isaplanner.prop_03.ctx -> isaplanner.prop_03.proof3 ),
      "isaplanner.prop_06.1" -> Later( isaplanner.prop_06.ctx -> isaplanner.prop_06.proof1 ),
      "isaplanner.prop_06.2" -> Later( isaplanner.prop_06.ctx -> isaplanner.prop_06.proof2 ),
      "isaplanner.prop_06.3" -> Later( isaplanner.prop_06.ctx -> isaplanner.prop_06.proof3 ),
      "isaplanner.prop_06.4" -> Later( isaplanner.prop_06.ctx -> isaplanner.prop_06.proof4 ),
      "isaplanner.prop_06.5" -> Later( isaplanner.prop_06.ctx -> isaplanner.prop_06.proof5 ),
      "isaplanner.prop_07.1" -> Later( isaplanner.prop_07.ctx -> isaplanner.prop_07.proof ),
      "isaplanner.prop_07.2" -> Later( isaplanner.prop_07.ctx -> isaplanner.prop_07.proof2 ),
      "isaplanner.prop_08.1" -> Later( isaplanner.prop_08.ctx -> isaplanner.prop_08.proof1 ),
      "isaplanner.prop_08.2" -> Later( isaplanner.prop_08.ctx -> isaplanner.prop_08.proof2 ),
      "isaplanner.prop_08.3" -> Later( isaplanner.prop_08.ctx -> isaplanner.prop_08.proof3 ),
      "isaplanner.prop_09.1" -> Later( isaplanner.prop_09.ctx -> isaplanner.prop_09.proof1 ),
      "isaplanner.prop_09.2" -> Later( isaplanner.prop_09.ctx -> isaplanner.prop_09.proof2 ),
      "isaplanner.prop_09.3" -> Later( isaplanner.prop_09.ctx -> isaplanner.prop_09.proof3 ),
      "isaplanner.prop_09.4" -> Later( isaplanner.prop_09.ctx -> isaplanner.prop_09.proof4 ),
      "isaplanner.prop_09.5" -> Later( isaplanner.prop_09.ctx -> isaplanner.prop_09.proof5 ),
      "isaplanner.prop_10.1" -> Later( isaplanner.prop_10.ctx -> isaplanner.prop_10.proof ),
      "isaplanner.prop_10.2" -> Later( isaplanner.prop_10.ctx -> isaplanner.prop_10.proof2 ),
      "isaplanner.prop_10.3" -> Later( isaplanner.prop_10.ctx -> isaplanner.prop_10.proof3 ),
      "isaplanner.prop_10.4" -> Later( isaplanner.prop_10.ctx -> isaplanner.prop_10.proof4 ),
      "isaplanner.prop_11" -> Later( isaplanner.prop_11.ctx -> isaplanner.prop_11.proof ),
      "isaplanner.prop_12" -> Later( isaplanner.prop_12.ctx -> isaplanner.prop_12.proof ),
      "isaplanner.prop_13" -> Later( isaplanner.prop_13.ctx -> isaplanner.prop_13.proof ),
      "isaplanner.prop_14" -> Later( isaplanner.prop_14.ctx -> isaplanner.prop_14.proof ),
      "isaplanner.prop_15" -> Later( isaplanner.prop_15.ctx -> isaplanner.prop_15.proof ),
      "isaplanner.prop_16" -> Later( isaplanner.prop_16.ctx -> isaplanner.prop_16.proof ),
      "isaplanner.prop_17" -> Later( isaplanner.prop_17.ctx -> isaplanner.prop_17.proof ),
      "isaplanner.prop_18" -> Later( isaplanner.prop_18.ctx -> isaplanner.prop_18.proof ),
      "isaplanner.prop_19" -> Later( isaplanner.prop_19.ctx -> isaplanner.prop_19.proof ),
      "isaplanner.prop_21" -> Later( isaplanner.prop_21.ctx -> isaplanner.prop_21.proof ),
      "isaplanner.prop_22" -> Later( isaplanner.prop_22.ctx -> isaplanner.prop_22.proof ),
      "isaplanner.prop_23" -> Later( isaplanner.prop_23.ctx -> isaplanner.prop_23.proof ),
      "isaplanner.prop_24.1" -> Later( isaplanner.prop_24.ctx -> isaplanner.prop_24.proof1 ),
      "isaplanner.prop_24.2" -> Later( isaplanner.prop_24.ctx -> isaplanner.prop_24.proof2 ),
      "isaplanner.prop_26" -> Later( isaplanner.prop_26.ctx -> isaplanner.prop_26.proof ),
      "isaplanner.prop_27" -> Later( isaplanner.prop_27.ctx -> isaplanner.prop_27.proof ),
      "isaplanner.prop_28" -> Later( isaplanner.prop_28.ctx -> isaplanner.prop_28.proof ),
      "isaplanner.prop_29" -> Later( isaplanner.prop_29.ctx -> isaplanner.prop_29.proof ),
      "isaplanner.prop_30" -> Later( isaplanner.prop_30.ctx -> isaplanner.prop_30.proof ),
      "isaplanner.prop_31" -> Later( isaplanner.prop_31.ctx -> isaplanner.prop_31.proof ),
      "isaplanner.prop_32" -> Later( isaplanner.prop_32.ctx -> isaplanner.prop_32.proof ),
      "isaplanner.prop_33" -> Later( isaplanner.prop_33.ctx -> isaplanner.prop_33.proof ),
      "isaplanner.prop_34" -> Later( isaplanner.prop_34.ctx -> isaplanner.prop_34.proof ),
      "isaplanner.prop_35" -> Later( isaplanner.prop_35.ctx -> isaplanner.prop_35.proof ),
      "isaplanner.prop_36" -> Later( isaplanner.prop_36.ctx -> isaplanner.prop_36.proof ),
      "isaplanner.prop_37" -> Later( isaplanner.prop_37.ctx -> isaplanner.prop_37.proof ),
      "isaplanner.prop_38" -> Later( isaplanner.prop_38.ctx -> isaplanner.prop_38.proof ),
      "isaplanner.prop_39" -> Later( isaplanner.prop_39.ctx -> isaplanner.prop_39.proof ),
      "isaplanner.prop_40" -> Later( isaplanner.prop_40.ctx -> isaplanner.prop_40.proof ),
      "isaplanner.prop_41" -> Later( isaplanner.prop_41.ctx -> isaplanner.prop_41.proof ),
      "isaplanner.prop_42" -> Later( isaplanner.prop_42.ctx -> isaplanner.prop_42.proof ),
      "isaplanner.prop_43" -> Later( isaplanner.prop_43.ctx -> isaplanner.prop_43.proof1 ),
      "isaplanner.prop_44" -> Later( isaplanner.prop_44.ctx -> isaplanner.prop_44.proof1 ),
      "isaplanner.prop_45" -> Later( isaplanner.prop_45.ctx -> isaplanner.prop_45.proof ),
      "isaplanner.prop_46" -> Later( isaplanner.prop_46.ctx -> isaplanner.prop_46.proof ),
      "isaplanner.prop_47" -> Later( isaplanner.prop_47.ctx -> isaplanner.prop_47.proof ),
      "isaplanner.prop_48" -> Later( isaplanner.prop_48.ctx -> isaplanner.prop_48.manualProof ),
      "isaplanner.prop_49" -> Later( isaplanner.prop_49.ctx -> isaplanner.prop_49.proof ),
      "isaplanner.prop_59" -> Later( isaplanner.prop_59.ctx -> isaplanner.prop_59.proof_1 ),
      "prod.prop_01.1" -> Later( prod.prop_01.ctx -> prod.prop_01.proof ),
      "prod.prop_01.2" -> Later( prod.prop_01.ctx -> prod.prop_01.singleInduction ),
      "prod.prop_01.3" -> Later( prod.prop_01.ctx -> prod.prop_01.simpleInductionProof ),
      "prod.prop_01.4" -> Later( prod.prop_01.ctx -> prod.prop_01.treeGrammar ),
      "prod.prop_04.1" -> Later( prod.prop_04.ctx -> prod.prop_04.proof ),
      "prod.prop_04.2" -> Later( prod.prop_04.ctx -> prod.prop_04.openind ),
      "prod.prop_05.1" -> Later( prod.prop_05.ctx -> prod.prop_05.proof ),
      "prod.prop_05.2" -> Later( prod.prop_05.ctx -> prod.prop_05.openind ),
      "prod.prop_06" -> Later( prod.prop_06.ctx -> prod.prop_06.proof ),
      "prod.prop_07" -> Later( prod.prop_07.ctx -> prod.prop_07.proof ),
      "prod.prop_08" -> Later( prod.prop_08.ctx -> prod.prop_08.proof ),
      "prod.prop_10.1" -> Later( prod.prop_10.ctx -> prod.prop_10.proof ),
      "prod.prop_10.2" -> Later( prod.prop_10.ctx -> prod.prop_10.openind ),
      "prod.prop_13" -> Later( prod.prop_13.ctx -> prod.prop_13.proof ),
      "prod.prop_15.1" -> Later( prod.prop_15.ctx -> prod.prop_15.proof ),
      "prod.prop_15.2" -> Later( prod.prop_15.ctx -> prod.prop_15.openind ),
      "prod.prop_16.1" -> Later( prod.prop_16.ctx -> prod.prop_16.proof ),
      "prod.prop_16.2" -> Later( prod.prop_16.ctx -> prod.prop_16.openind ),
      "prod.prop_20.1" -> Later( prod.prop_20.ctx -> prod.prop_20.proof ),
      "prod.prop_20.2" -> Later( prod.prop_20.ctx -> prod.prop_20.openind ),
      "prod.prop_27" -> Later( prod.prop_27.ctx -> prod.prop_27.proof ),
      "prod.prop_28" -> Later( prod.prop_28.ctx -> prod.prop_28.proof ),
      "prod.prop_29" -> Later( prod.prop_29.ctx -> prod.prop_29.proof ),
      "prod.prop_30" -> Later( prod.prop_30.ctx -> prod.prop_30.proof ),
      "prod.prop_31" -> Later( prod.prop_31.ctx -> prod.prop_31.revrev ),
      "prod.prop_32" -> Later( prod.prop_32.ctx -> prod.prop_32.proof ),
      "prod.prop_33" -> Later( prod.prop_33.ctx -> prod.prop_33.proof ),
      "prod.prop_34" -> Later( prod.prop_34.ctx -> prod.prop_34.proof ),
      "prod.prop_35" -> Later( prod.prop_35.ctx -> prod.prop_35.proof ) )

  args.toList match {
    case Seq( "--list" ) => indProofs.keys.toSeq.sorted.foreach( println )
    case Seq( name ) =>
      val ( ctx0, proof ) = indProofs( name ).value
      implicit val ctx = ctx0.newMutable

      val exp = eliminateCutsET( deskolemizeET( LKToExpansionProof( proof ) ) )
      val ETWeakQuantifier( _, insts ) = exp.inductions.head.suc
      val term = insts.head._1.asInstanceOf[Var]

      val ETStrongQuantifierBlock( _, xs, _ ) = exp.expansionSequent.succedent.head
      require( xs.contains( term ) )
      val Right( proof1 ) = ExpansionProofToLK( exp )
      val proof2 =
        instanceProof( proof1, for ( x <- xs ) yield if ( x == term ) term else {
          val c = Const( ctx.newNameGenerator.fresh( x.name ), x.ty )
          ctx += c
          c
        } )
      val proof3 = ForallRightRule( proof2, All( term, proof2.endSequent.succedent.head ) )
      val p = proof3

      val qtys =
        try {
          val indG = extractInductionGrammar( p )
          println( s"SIP with induction grammar:\n$indG" )
          Some( indG.gamma.map { case Var( _, TBase( n, _ ) ) => n } )
        } catch {
          case ex: Throwable =>
            ex.printStackTrace()
            None
        }

      verbose.only( TreeGrammarProver.logger ) {
        indElimReversal( p, TreeGrammarProverOptions( minInstProof = false, quantTys = qtys ) )
        TreeGrammarProver( p.endSequent )
      }
  }

}
