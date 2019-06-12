package gapt.testing
import cats.{ Eval, Later }
import gapt.examples.Script
import gapt.examples.theories._
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.expr.util.typeVariables
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.expansion._
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.lk._
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.util.extractInductionGrammar
import gapt.proofs.lk.util.instanceProof
import gapt.provers.viper.grammars.{ TreeGrammarProver, TreeGrammarProverOptions, indElimReversal }
import gapt.utils.LogHandler.VerbosityLevel
import gapt.utils.{ LogHandler, Logger, MetricsPrinter, MetricsPrinterWithMessages, verbose }

object sipReconstruct extends Script {

  def accessField( obj: AnyRef, fieldName: String ): AnyRef =
    obj.getClass.getMethod( fieldName ).invoke( obj )

  def getProofs( name: String, obj: => TacticsProof, proofs: String* ): Seq[( String, Eval[( Context, LKProof )] )] =
    proofs.map( pn => s"$name.$pn" -> Later( obj.ctx -> accessField( obj, pn ).asInstanceOf[LKProof] ) )

  // do not do this at home
  def tip( name: String, proofs: String* ) = {
    val baseClass: Class[_] = gapt.examples.tip.`package`.getClass
    val className = s"${baseClass.getPackage.getName}.$name$$"
    getProofs(
      name,
      baseClass.getClassLoader.loadClass( className ).
        getField( "MODULE$" ).get( null ).asInstanceOf[TacticsProof],
      proofs: _* )
  }

  def getIsaplanner( name: String, proofs: String* ) =
    tip( s"isaplanner.prop_$name", proofs: _* )
  def getProd( name: String, proofs: String* ) =
    tip( s"prod.prop_$name", proofs: _* )

  def inlineLast( thy: Theory )( lem: thy.LemmaHandle ): LKProof =
    if ( lem.usedLemmas.isEmpty ) lem.proof else {
      val n = lem.usedLemmas.maxBy( _.number ).name
      lem.combined( included = Set( n ) )
    }

  def groundTypeVars( p: LKProof )( implicit ctx: Context ): ( Context, LKProof ) = {
    val mutCtx = ctx.newMutable
    val tyVars = typeVariables( p.endSequent.elements )
    val nameGen = mutCtx.newNameGenerator
    val grounding = tyVars.map( v => v -> TBase( nameGen.fresh( v.name ) ) ).toMap
    grounding.values.foreach( mutCtx += _ )
    mutCtx.toImmutable -> Substitution( Map.empty, grounding )( p )
  }

  val indProofs = ( Map()
    ++ getIsaplanner( "03", "proof", "proof2", "proof3" )
    ++ getIsaplanner( "06", "proof1", "proof2", "proof3", "proof4", "proof5" )
    ++ getIsaplanner( "07", "proof", "proof2" )
    ++ getIsaplanner( "08", "proof1", "proof2", "proof3" )
    ++ getIsaplanner( "09", "proof1", "proof2", "proof3", "proof4", "proof5" )
    ++ getIsaplanner( "10", "proof", "proof2", "proof3", "proof4" )
    ++ getIsaplanner( "11", "proof" )
    ++ getIsaplanner( "12", "proof" )
    ++ getIsaplanner( "13", "proof" )
    ++ getIsaplanner( "14", "proof" )
    ++ getIsaplanner( "15", "proof" )
    ++ getIsaplanner( "16", "proof" )
    ++ getIsaplanner( "17", "proof" )
    ++ getIsaplanner( "18", "proof" )
    ++ getIsaplanner( "19", "proof" )
    ++ getIsaplanner( "21", "proof" )
    ++ getIsaplanner( "22", "proof" )
    ++ getIsaplanner( "23", "proof" )
    ++ getIsaplanner( "24", "proof1", "proof2" )
    ++ getIsaplanner( "26", "proof" )
    ++ getIsaplanner( "27", "proof" )
    ++ getIsaplanner( "28", "proof" )
    ++ getIsaplanner( "29", "proof" )
    ++ getIsaplanner( "30", "proof" )
    ++ getIsaplanner( "31", "proof" )
    ++ getIsaplanner( "32", "proof" )
    ++ getIsaplanner( "33", "proof" )
    ++ getIsaplanner( "34", "proof" )
    ++ getIsaplanner( "35", "proof" )
    ++ getIsaplanner( "36", "proof" )
    ++ getIsaplanner( "37", "proof" )
    ++ getIsaplanner( "38", "proof" )
    ++ getIsaplanner( "39", "proof", "proof2" )
    ++ getIsaplanner( "40", "proof" )
    ++ getIsaplanner( "41", "proof" )
    ++ getIsaplanner( "42", "proof" )
    ++ getIsaplanner( "43", "proof1" )
    ++ getIsaplanner( "44", "proof1" )
    ++ getIsaplanner( "45", "proof" )
    ++ getIsaplanner( "46", "proof" )
    ++ getIsaplanner( "47", "proof" )
    ++ getIsaplanner( "48", "manualProof" )
    ++ getIsaplanner( "49", "proof" )
    ++ getIsaplanner( "59", "proof_1" )
    ++ getProd( "01", "proof", "singleInduction", "simpleInductionProof", "treeGrammar" )
    ++ getProd( "04", "proof", "openind" )
    ++ getProd( "05", "proof", "openind" )
    ++ getProd( "06", "proof" )
    ++ getProd( "07", "proof", "proof2" )
    ++ getProd( "08", "proof" )
    ++ getProd( "10", "proof", "openind" )
    ++ getProd( "13", "proof" )
    ++ getProd( "15", "proof", "openind" )
    ++ getProd( "16", "proof", "openind" )
    ++ getProd( "20", "proof", "openind" )
    ++ getProd( "27", "proof" )
    ++ getProd( "28", "proof" )
    ++ getProd( "29", "proof" )
    ++ getProd( "30", "proof" )
    ++ getProd( "31", "revrev" )
    ++ getProd( "32", "proof" )
    ++ getProd( "33", "proof" )
    ++ getProd( "34", "proof" )
    ++ getProd( "35", "proof" )
    ++ {
      val thy = new Theory(
        nat, natorder, natdivision, natdivisible,
        list, listlength, listdrop, listfold )
      import thy._
      // Blacklist: contain partially applied functions
      val blacklist = Set( "foldrapp", "filterapp", "lallapp", "lallrev",
        "lenmap", "mapapp", "mapmap", "revfilter", "revmap" )
      allProofs.view.filterNot( p => blacklist( p._1 ) ).flatMap( p => Seq(
        s"theory.${p._1}" -> Later( groundTypeVars( LemmaHandle( p._1 ).proof ) ),
        s"theory1.${p._1}" -> Later( groundTypeVars( inlineLast( thy )( LemmaHandle( p._1 ) ) ) ) ) )
    } )

  args.toList match {
    case Seq( "--list" ) => indProofs.keys.toSeq.sorted.foreach( println )
    case Seq( name, atp, interp, minProof ) =>
      go( name, atp.toBoolean, interp.toBoolean, minProof.toBoolean )
  }

  def go( name: String, atp: Boolean, interp: Boolean, minProof: Boolean ): Unit = {
    val logger = Logger( "sipReconstruct" )
    val metricsPrinter = new MetricsPrinterWithMessages
    LogHandler.current.value = metricsPrinter
    logger.metric( "proof", name )
    logger.metric( "atp", atp )
    logger.metric( "use_interp", interp )
    logger.metric( "min_proof", minProof )

    try {
      val ( ctx0, proof ) = indProofs( name ).value
      implicit val ctx = ctx0.newMutable

      val sip = try {
        val Sequent( _, Seq( All.Block( xs, _ ) ) ) = proof.endSequent
        logger.metric( "univvars", xs.size )
        val proof0 = normalizeLKt.lk( instanceProof( proof, xs ) )

        val exp = eliminateCutsET( deskolemizeET( prenexifyET.exceptTheory( LKToExpansionProof( proof0 ) ) ) )
        val ETWeakQuantifier( _, insts ) = exp.inductions.head.suc
        val term = insts.head._1.asInstanceOf[Var]

        require( xs.contains( term ) )
        val Right( proof1 ) = ExpansionProofToLK( exp )
        val proof2 = Substitution( for ( x <- xs if x != term ) yield x -> {
          val c = Const( ctx.newNameGenerator.fresh( x.name ), x.ty )
          ctx += c
          c
        } )( proof1 )
        val proof3 = ForallRightRule( proof2, All( term, proof2.endSequent.succedent.head ) )
        proof3
      } catch {
        case _: Throwable =>
          logger.metric( "is_sip", false )
          return
      }
      logger.metric( "is_sip", true )

      val indG = extractInductionGrammar( sip )
      println( s"SIP with induction grammar:\n$indG" )
      logger.metric( "sip_ind_gram_size", indG.size )
      for ( InductionRule( _, Abs( x, f ), _ ) <- sip.subProofs )
        logger.metric( "sip_ind_form", f.toSigRelativeString )
      val qtys = indG.gamma.map { case Var( _, t @ TBase( _, _ ) ) => t }
      logger.metric( "sip_prob", sip.endSequent.succedent.head.toSigRelativeString )

      val opts = TreeGrammarProverOptions(
        quantTys = Some( qtys ),
        minInstProof = minProof,
        useInterpolation = interp )
      val indp = verbose.only( TreeGrammarProver.logger ) {
        if ( atp ) TreeGrammarProver( sip.endSequent, opts )
        else indElimReversal( sip, opts )
      }
      logger.metric( "success", true )
    } catch {
      case e: Throwable =>
        logger.metric(
          "exception",
          Option( e.getMessage ).getOrElse( e.getClass.getSimpleName ).take( 100 ) )
        throw e
    }
  }

}
