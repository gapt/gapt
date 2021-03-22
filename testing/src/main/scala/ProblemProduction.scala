package gapt.testing

import gapt.examples.theories._
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.expr.ty.Ty
import gapt.expr.util.typeVariables
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.expansion._
import gapt.proofs.lk._
<<<<<<< HEAD
import gapt.proofs.reduction._
=======
<<<<<<< HEAD
import gapt.proofs.reduction._
=======
import gapt.proofs.reduction.ErasureReductionET
>>>>>>> 6f1e56c47597225175de980bdf406a8d162966f3
>>>>>>> a5277f887e23efddcf1ba5cf22d1fd410c136a94
import gapt.expr.formula.hol.instantiate
import gapt.proofs.lk.rules.ForallRightRule
import gapt.formats.tptp.TptpFOLExporter
import gapt.provers.viper.grammars.EnumeratingInstanceGenerator
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.{ FOLClause, HOLClause, HOLSequent, Sequent }
import gapt.provers.groundFreeVariables
import java.io.File
import java.io.PrintWriter

object ProblemProduction {
  def accessField( obj: AnyRef, fieldName: String ): AnyRef =
    obj.getClass.getMethod( fieldName ).invoke( obj )

  def tip( name: String, seqName: String ) = {
    val baseClass: Class[_] = gapt.examples.tip.`package`.getClass
    val className = s"${baseClass.getPackage.getName}.$name$$"
    val obj = baseClass.getClassLoader.loadClass( className ).getField( "MODULE$" ).get( null ).asInstanceOf[TacticsProof]
    print( "Problem " + className + " Loaded\n" )
    ( name.replace( '.', '_' ) -> ( accessField( obj, seqName ).asInstanceOf[Sequent[( String, gapt.expr.formula.Formula )]], obj.ctx ) )
  }

  def getIsaplanner( name: String, seqName: String ) =
    tip( s"isaplanner.prop_$name", seqName )

  def getProd( name: String, seqName: String ) =
    tip( s"prod.prop_$name", seqName )
  // As suggested in sipReconstruct.scala, to not try at home
  val indProofs = ( Map()
<<<<<<< HEAD
    //+ getIsaplanner( "03", "sequent" )
    // + getIsaplanner( "06", "sequent" )
    // + getIsaplanner( "07", "sequent" )
    // + getIsaplanner( "08", "sequent" )
    // + getIsaplanner( "09", "sequent" )
    + getIsaplanner( "10", "sequent" )
    + getIsaplanner( "11", "sequent" )
  // + getIsaplanner( "12", "sequent" )
  //  + getIsaplanner( "13", "sequent" )
  // + getIsaplanner( "14", "sequent" )
  // + getIsaplanner( "15", "sequent" )
  // + getIsaplanner( "16", "sequent" )
  //+ getIsaplanner( "17", "sequent" )
=======
<<<<<<< HEAD
    + getIsaplanner( "03", "sequent" )
  // + getIsaplanner( "06", "sequent" )
  // + getIsaplanner( "07", "sequent" )
  // + getIsaplanner( "08", "sequent" )
  // + getIsaplanner( "09", "sequent" )
  // + getIsaplanner( "10", "sequent" )
  // + getIsaplanner( "11", "sequent" )
  // + getIsaplanner( "12", "sequent" )
  // + getIsaplanner( "13", "sequent" )
  // + getIsaplanner( "14", "sequent" )
  // + getIsaplanner( "15", "sequent" )
  // + getIsaplanner( "16", "sequent" )
  // + getIsaplanner( "17", "sequent" )
>>>>>>> a5277f887e23efddcf1ba5cf22d1fd410c136a94
  // + getIsaplanner( "18", "sequent" )
  // + getIsaplanner( "19", "sequent" )
  // + getIsaplanner( "21", "sequent" )
  // + getIsaplanner( "22", "sequent" )
  // + getIsaplanner( "23", "sequent" )
  // + getIsaplanner( "24", "sequent" )
  // + getIsaplanner( "26", "sequent" )
  // + getIsaplanner( "27", "sequent" )
  // + getIsaplanner( "28", "sequent" )
  // + getIsaplanner( "29", "sequent" )
  // + getIsaplanner( "30", "sequent" )
  // + getIsaplanner( "31", "sequent" )
  // + getIsaplanner( "32", "sequent" )
  // + getIsaplanner( "33", "sequent" )
  // + getIsaplanner( "34", "sequent" )
  // + getIsaplanner( "35", "sequent" )
  // + getIsaplanner( "36", "sequent" )
  // + getIsaplanner( "37", "sequent" )
  // + getIsaplanner( "38", "sequent" )
  // + getIsaplanner( "39", "sequent" )
  // + getIsaplanner( "40", "sequent" )
  // + getIsaplanner( "41", "sequent" )
  // + getIsaplanner( "42", "sequent" )
  // + getIsaplanner( "43", "sequent" )
  // + getIsaplanner( "44", "sequent" )
  // + getIsaplanner( "45", "sequent" )
  // + getIsaplanner( "46", "sequent" )
  // + getIsaplanner( "47", "sequent" )
  // + getIsaplanner( "48", "sequent" )
  // + getIsaplanner( "49", "sequent" )
  // + getIsaplanner( "59", "sequent" )
  // + getProd( "01", "sequent" )
  // + getProd( "04", "sequent" )
  // + getProd( "05", "sequent" )
  // + getProd( "06", "sequent" )
  // + getProd( "07", "sequent" )
  // + getProd( "08", "sequent" )
  // + getProd( "10", "sequent" )
  // + getProd( "13", "sequent" )
  // + getProd( "15", "sequent" )
  // + getProd( "16", "sequent" )
  // + getProd( "20", "sequent" )
  // + getProd( "27", "sequent" )
  // + getProd( "28", "sequent" )
  // + getProd( "29", "sequent" )
  // + getProd( "30", "sequent" )
  //  + getProd( "31", "sequent" ) //too long to load
<<<<<<< HEAD
=======
=======
    // + getIsaplanner( "03", "sequent" )
    // + getIsaplanner( "06", "sequent" )
    // + getIsaplanner( "07", "sequent" )
    // + getIsaplanner( "08", "sequent" )
    // + getIsaplanner( "09", "sequent" )
    // + getIsaplanner( "10", "sequent" )
    // + getIsaplanner( "11", "sequent" )
    // + getIsaplanner( "12", "sequent" )
    + getIsaplanner( "13", "sequent" )
    // + getIsaplanner( "14", "sequent" )
    // + getIsaplanner( "15", "sequent" )
    // + getIsaplanner( "16", "sequent" )
    // + getIsaplanner( "17", "sequent" )
    // + getIsaplanner( "18", "sequent" )
    // + getIsaplanner( "19", "sequent" )
    // + getIsaplanner( "21", "sequent" )
    // + getIsaplanner( "22", "sequent" )
    // + getIsaplanner( "23", "sequent" )
    // + getIsaplanner( "24", "sequent" )
    // + getIsaplanner( "26", "sequent" )
    // + getIsaplanner( "27", "sequent" )
    // + getIsaplanner( "28", "sequent" )
    // + getIsaplanner( "29", "sequent" )
    // + getIsaplanner( "30", "sequent" )
    // + getIsaplanner( "31", "sequent" )
    // + getIsaplanner( "32", "sequent" )
    // + getIsaplanner( "33", "sequent" )
    // + getIsaplanner( "34", "sequent" )
    // + getIsaplanner( "35", "sequent" )
    // + getIsaplanner( "36", "sequent" )
    // + getIsaplanner( "37", "sequent" )
    // + getIsaplanner( "38", "sequent" )
    // + getIsaplanner( "39", "sequent" )
    // + getIsaplanner( "40", "sequent" )
    // + getIsaplanner( "41", "sequent" )
    // + getIsaplanner( "42", "sequent" )
    // + getIsaplanner( "43", "sequent" )
    // + getIsaplanner( "44", "sequent" )
    // + getIsaplanner( "45", "sequent" )
    // + getIsaplanner( "46", "sequent" )
    // + getIsaplanner( "47", "sequent" )
    // + getIsaplanner( "48", "sequent" )
    // + getIsaplanner( "49", "sequent" )
    // + getIsaplanner( "59", "sequent" )
    // + getProd( "01", "sequent" )
    // + getProd( "04", "sequent" )
    // + getProd( "05", "sequent" )
    // + getProd( "06", "sequent" )
    // + getProd( "07", "sequent" )
    // + getProd( "08", "sequent" )
    // + getProd( "10", "sequent" )
    // + getProd( "13", "sequent" )
    // + getProd( "15", "sequent" )
    // + getProd( "16", "sequent" )
    // + getProd( "20", "sequent" )
    // + getProd( "27", "sequent" )
    // + getProd( "28", "sequent" )
    // + getProd( "29", "sequent" )
    // + getProd( "30", "sequent" )
    + getProd( "31", "sequent" ) //too long to load
>>>>>>> 6f1e56c47597225175de980bdf406a8d162966f3
>>>>>>> a5277f887e23efddcf1ba5cf22d1fd410c136a94
  //+ getProd( "32", "sequent" )
  //+ getProd( "33", "sequent" )
  //+ getProd( "34", "sequent" )
  //+ getProd( "35", "sequent" )

  )
  val produceProblems = {
    var ret = Map[String, Sequent[( String, gapt.expr.formula.Formula )]]()
    for ( tup <- indProofs )
      for ( pairs <- process( tup._1, tup._2._1, tup._2._2 ) )
        ret = ret + pairs
    ret
  }
  val asTptpProbs = produceProblems.map( p => {
    print( p._1 )
    try {
<<<<<<< HEAD
      val reduction = PredicateReductionET |> ErasureReductionET
=======
<<<<<<< HEAD
      val reduction = CNFReductionLKRes |> PredicateReductionCNF |> ErasureReductionCNF
=======
      val reduction = ErasureReductionET
>>>>>>> 6f1e56c47597225175de980bdf406a8d162966f3
>>>>>>> a5277f887e23efddcf1ba5cf22d1fd410c136a94
      val ( folProblem, back ) = reduction forward ( groundFreeVariables( p._2 )._1 ) //TermReplacement.undoGrounding for the reverse action
      val ret = TptpFOLExporter( folProblem )
      print( " is complete" + "\n" )
      Some( p._1 -> ret )
    } catch {
      case e: Exception => {
        print( " Failed" + "\n" )
        None
      }
    }
  } ).flatten

  def constructFiles( location: String = "PLCOPProblems" ) = {
    val ProbDicName = "PLCOPProblems"
    val instDicName = "instantiations/"
    val innerinstDicName = "instances/"
    val proofsDicName = "proofs/"
    val fileDic = new File( ProbDicName + "/" )
    if ( !fileDic.exists() ) fileDic.mkdir()
    for ( pair <- asTptpProbs ) {
      val dicSplit = pair._1.split( "_", 4 )
      val outerDic = dicSplit( 0 )
      val fileOuterDic = new File( ProbDicName + "/" + outerDic )
      if ( !fileOuterDic.exists() ) fileOuterDic.mkdir()
      val innerDic = dicSplit( 1 ) + "_" + dicSplit( 2 )
      val fileInnerDic = new File( ProbDicName + "/" + outerDic + "/" + innerDic )
      if ( !fileInnerDic.exists() ) fileInnerDic.mkdir()
      val fileInstDic = new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName )
      if ( !fileInstDic.exists() ) fileInstDic.mkdir()
      val split2 = dicSplit( 3 ).split( "\\(" )
      val insttypedic = new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName + split2( 0 ) )
      if ( !insttypedic.exists() ) insttypedic.mkdir()
      val innerinstdic = new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName + split2( 0 ) + "/" + innerinstDicName )
      if ( !innerinstdic.exists() ) innerinstdic.mkdir()
      val proofsDicdic = new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName + split2( 0 ) + "/" + proofsDicName )
      if ( !proofsDicdic.exists() ) proofsDicdic.mkdir()
      val file = "instance_" + split2( 1 ).split( "\\)" )( 0 ) + ".tptp"
      val finalfile = new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName + split2( 0 ) + "/" + innerinstDicName + file )
      if ( !finalfile.exists() ) {
        val writer = new PrintWriter( new File( ProbDicName + "/" + outerDic + "/" + innerDic + "/" + instDicName + split2( 0 ) + "/" + innerinstDicName + file ) )
        writer.write( pair._2.toString )
        writer.close
      }
    }
  }

  def process( name: String, seq: Sequent[( String, gapt.expr.formula.Formula )], ctx: Context ): Map[String, Sequent[( String, gapt.expr.formula.Formula )]] = {
    val Sequent( theory, Seq( ( word, All.Block( xs: Seq[Var], f ) ) ) ) = seq
    val skolVals = xs.map( va => ( va -> Const( va.name + "bb", va.ty ) ) ).toMap
    val varWithInst = xs.map( va => ( va, xs ) ).map( dup => {
      val indTy = dup._1.ty.asInstanceOf[TBase]
      val instanceGen = new EnumeratingInstanceGenerator( Seq( indTy ), false, ctx )
<<<<<<< HEAD
      val instances = ( if ( indTy.toString == "list" ) instanceGen.generate( 0, 20, 10 ) else instanceGen.generate( 0, 10, 10 ) ).toSeq.flatten
=======
      val instances = ( if ( indTy.toString == "list" ) instanceGen.generate( 0, 20, 20 ) else instanceGen.generate( 0, 10, 10 ) ).toSeq.flatten
>>>>>>> a5277f887e23efddcf1ba5cf22d1fd410c136a94
      val names = ( 1 to 10 toList ).map( s => s.toString )
      val instWithName = instances zip names
      instWithName.map( ins => ( dup._1, ins, dup._2 ) ).toSeq
    } )
    val instTrips = varWithInst.fold( Seq() )( ( a, b ) => a ++ b )

    val quantInst = instTrips.map( inst => {
      inst._3.map( vals => {
        if ( vals.name == inst._1.name ) ( "1", inst._2._2, inst._2._1 )
        else skolVals.get( vals ) match {
          case Some( t ) => ( "0", "", t )
          case None      => ( "0", "", Const( "bb", vals.ty ) )
        }
      } ).toSeq
    } )
    quantInst.map( inst => {
      val nameInstPair = inst.unzip3
      val newNamePart = nameInstPair._1.fold( name )( ( a, b ) => a + "_" + b )
      val newName = nameInstPair._2.fold( newNamePart + "(" )( ( a, b ) => a + b ) + ")"
      val newSequent = Sequent( theory, Seq( ( word, instantiate( All.Block( xs, f ), nameInstPair._3 ) ) ) )
      ( newName -> newSequent )
    } ).toMap
  }
}
