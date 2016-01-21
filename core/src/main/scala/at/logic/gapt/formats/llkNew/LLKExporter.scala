package at.logic.gapt.formats.llkNew

import at.logic.gapt.proofs._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk._

object LatexLLKExporter extends LLKExporter( true )
object LLKExporter extends LLKExporter( false )

class LLKExporter( val expandTex: Boolean ) {
  val emptyTypeMap = Map[String, Ty]()
  val nLine = sys.props( "line.separator" )

  def apply( db: ExtendedProofDatabase, escape_latex: Boolean ) = {
    val types0 = db.eproofs.foldLeft( ( emptyTypeMap, emptyTypeMap ) )( ( t, p ) =>
      getTypes( p._2, t._1, t._2 ) )
    val types1 = db.axioms.foldLeft( types0 )( ( m, fs ) => getTypes( fs, m._1, m._2 ) )
    val types2 = db.sequentLists.foldLeft( types1 )( ( m, el ) =>
      el._2.foldLeft( m )( ( m_, fs ) => getTypes( fs, m._1, m._2 ) ) )
    val ( vtypes, ctypes ) = db.eproofs.keySet.foldLeft( types2 )( ( m, x ) => getTypes( x, m._1, m._2 ) )

    val sb = new StringBuilder()
    sb.append( generateDeclarations( vtypes, ctypes ) )
    sb.append( nLine + nLine )
    for ( p <- db.eproofs ) {
      sb.append( generateProof( p._2, "", escape_latex ) )
      sb.append( nLine )
      sb.append( "\\CONTINUEWITH{" + toLatexString.getFormulaString( p._1, true, escape_latex ) + "}" )
      sb.append( nLine )
    }

    sb.toString()
  }

  def apply( lkp: LKProof, escape_latex: Boolean ) = {
    val ( vtypes, ctypes ) = getTypes( lkp, emptyTypeMap, emptyTypeMap )
    val declarations = generateDeclarations( vtypes, ctypes )
    val proofs = generateProof( lkp, "", escape_latex )

    declarations + nLine + "\\CONSTDEC{THEPROOF}{o}" + nLine + nLine + proofs + "\\CONTINUEWITH{THEPROOF}"
  }

  def generateDeclarations( vars: Map[String, Ty], consts: Map[String, Ty] ): String = {

    val svars = vars.foldLeft( Map[String, String]() )( ( map, p ) => {
      val vname = toLatexString.nameToLatexString( p._1.toString )
      if ( map contains vname ) throw new Exception( "Two different kinds of symbol share the same name!" )
      map + ( ( vname, getTypeString( p._2 ) ) )
    } )
    val sconsts = consts.foldLeft( Map[String, String]() )( ( map, p ) => {
      val vname = toLatexString.nameToLatexString( p._1.toString )
      if ( map contains vname ) throw new Exception( "Two different kinds of symbol share the same name!" )
      map + ( ( vname, getTypeString( p._2 ) ) )
    } ).filterNot( _._1 == "=" )
    /*
    val sdefs = defs.foldLeft(Map[String, String]())((map, p) => {
      val w = "[a-zA-Z0-9]+"
      val re= ("("+w+")\\[("+w+"(,"+w+")*"+")\\]").r
      val vname = toLatexString.nameToLatexString(p._1.toString, false)
      if (map contains vname) throw new Exception("Two different kinds of symbol share the same name!")
      map + ((vname, getTypeString(p._2)))
    })*/

    val rvmap = svars.foldLeft( Map[String, List[String]]() )( ( map, p ) => {
      val ( name, expt ) = p
      if ( map contains expt )
        map + ( ( expt, name :: map( expt ) ) )
      else
        map + ( ( expt, name :: Nil ) )
    } )

    val rcmap = sconsts.foldLeft( Map[String, List[String]]() )( ( map, p ) => {
      val ( name, expt ) = p
      if ( map contains expt )
        map + ( ( expt, name :: map( expt ) ) )
      else
        map + ( ( expt, name :: Nil ) )
    } )

    val sv = rvmap.map( x => "\\VARDEC{" + x._2.mkString( ", " ) + "}{" + x._1 + "}" )
    val sc = rcmap.map( x => "\\CONSTDEC{" + x._2.mkString( ", " ) + "}{" + x._1 + "}" )
    sv.mkString( nLine ) + nLine + sc.mkString( nLine )
  }

  def getTypes( p: LKProof, vacc: Map[String, Ty], cacc: Map[String, Ty] ): ( Map[String, Ty], Map[String, Ty] ) = {
    val formulas = for ( subProof <- p.subProofs; formula <- subProof.endSequent.elements ) yield formula
    formulas.foldLeft( ( vacc, cacc ) )( ( map, f ) =>
      getTypes( f, map._1, map._2 ) )
  }

  def getTypes( p: HOLSequent, vacc: Map[String, Ty], cacc: Map[String, Ty] ): ( Map[String, Ty], Map[String, Ty] ) = {
    p.formulas.foldLeft( ( vacc, cacc ) )( ( m, f ) => getTypes( f, m._1, m._2 ) )
  }

  def getTypes( exp: LambdaExpression, vmap: Map[String, Ty], cmap: Map[String, Ty] ): ( Map[String, Ty], Map[String, Ty] ) = exp match {
    case Var( name, exptype ) =>
      if ( vmap.contains( name ) ) {
        if ( vmap( name ) != exptype ) throw new Exception( "Symbol clash for " + name + " " + vmap( name ) + " != " + exptype )
        ( vmap, cmap )
      } else {
        ( vmap + ( ( name, exptype ) ), cmap )
      }

    case EqC( _ ) => ( vmap, cmap )

    case NonLogicalConstant( name, exptype ) =>
      val sym = exp.asInstanceOf[Const].sym
      if ( cmap.contains( name ) ) {
        if ( cmap( name ) != exptype ) throw new Exception( "Symbol clash for " + name + " " + cmap( name ) + " != " + exptype )
        ( vmap, cmap )
      } else {
        ( vmap, cmap + ( ( name, exptype ) ) )
      }

    case App( s, t ) =>
      val ( vm, cm ) = getTypes( t, vmap, cmap )
      getTypes( s, vm, cm )

    case Abs( x, t ) =>
      val ( vm, cm ) = getTypes( t, vmap, cmap )
      getTypes( x, vm, cm )

    case _: LogicalConstant =>
      ( vmap, cmap )
  }

  def getTypeString( t: Ty, outermost: Boolean = true ): String = t match {
    case Ti => "i"
    case To => "o"
    case t1 -> t2 =>
      val s = getTypeString( t1, false ) + ">" + getTypeString( t2, false )
      if ( outermost ) s else "(" + s + ")"
  }

  def fsequentString( fs: HOLSequent, escape_latex: Boolean ): String =
    fs.antecedent.map( toLatexString.getFormulaString( _, true, escape_latex ) ).mkString( "{", ",", "}" ) +
      fs.succedent.map( toLatexString.getFormulaString( _, true, escape_latex ) ).mkString( "{", ",", "}" )

  def generateProof( p: LKProof, s: String, escape_latex: Boolean ): String = p match {
    case InitialSequent( root ) =>
      "\\AX" + fsequentString( p.endSequent, escape_latex ) + nLine + s
    // unary rules
    case NegLeftRule( p1, _ ) =>
      generateProof( p1, "\\NEGL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case NegRightRule( p1, _ ) =>
      generateProof( p1, "\\NEGR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case AndLeftRule( p1, _, _ ) =>
      generateProof( p1, "\\ANDL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case OrRightRule( p1, _, _ ) =>
      generateProof( p1, "\\ORR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ImpRightRule( p1, _, _ ) =>
      generateProof( p1, "\\IMPR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    //binary rules
    case AndRightRule( p1, _, p2, _ ) =>
      generateProof( p1, generateProof( p2, "\\ANDR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex ), escape_latex )
    case OrLeftRule( p1, _, p2, _ ) =>
      generateProof( p1, generateProof( p2, "\\ORL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex ), escape_latex )
    case ImpLeftRule( p1, _, p2, _ ) =>
      generateProof( p1, generateProof( p2, "\\IMPL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex ), escape_latex )
    //structural rules
    case CutRule( p1, _, p2, _ ) =>
      generateProof( p1, generateProof( p2, "\\CUT" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex ), escape_latex )
    case WeakeningLeftRule( p1, _ ) =>
      generateProof( p1, "\\WEAKL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case WeakeningRightRule( p1, _ ) =>
      generateProof( p1, "\\WEAKR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ContractionLeftRule( p1, _, _ ) =>
      generateProof( p1, "\\CONTRL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ContractionRightRule( p1, _, _ ) =>
      generateProof( p1, "\\CONTRR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    //quantifier rules
    case ForallLeftRule( p1, aux, main, term, qv ) =>
      generateProof( p1, "\\ALLL{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ForallRightRule( p1, main, eigenvar, qv ) =>
      generateProof( p1, "\\ALLR{" + toLatexString.getFormulaString( eigenvar, true, escape_latex ) + "}" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ExistsLeftRule( p1, main, eigenvar, qv ) =>
      generateProof( p1, "\\EXL{" + toLatexString.getFormulaString( eigenvar, true, escape_latex ) + "}" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ExistsRightRule( p1, aux, main, term, qv ) =>
      generateProof( p1, "\\EXR{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    //equality rules
    case EqualityLeftRule( p1, _, _, _ ) =>
      generateProof( p1, "\\UEQL" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case EqualityRightRule( p1, _, _, _ ) =>
      generateProof( p1, "\\UEQR" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    //definition rules
    case DefinitionLeftRule( p1, _, _ ) =>
      generateProof( p1, "\\DEF" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case DefinitionRightRule( p1, _, _ ) =>
      generateProof( p1, "\\DEF" + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )

    //TODO: this is only a way to write out the proof, but it cannot be read back in (labels are not handled by llk so far)
    /*
    case ExistsSkLeftRule( p1,  aux, main, term ) =>
      generateProof( p1, "\\EXSKL{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}"
        + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ExistsSkRightRule( p1,  aux, main, term ) =>
      generateProof( p1, "\\EXSKR{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}"
        + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ForallSkLeftRule( p1,  aux, main, term ) =>
      generateProof( p1, "\\ALLSKL{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}"
        + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    case ForallSkRightRule( p1,  aux, main, term ) =>
      generateProof( p1, "\\ALLSKR{" + toLatexString.getFormulaString( term, true, escape_latex ) + "}"
        + fsequentString( p.endSequent, escape_latex ) + nLine + s, escape_latex )
    */
  }

}

/**
 * This is a prover9 style formatting which can be parsed by LLK.
 */
object toLLKString {
  def apply( e: LambdaExpression ) = toLatexString.getFormulaString( e, true, false )
}

/**
 * This is a Latex formatting which can be parsed by LLK.
 */
object toLatexString {
  def apply( e: LambdaExpression ) = getFormulaString( e, true, true )

  def getFormulaString( f: LambdaExpression, outermost: Boolean = true, escape_latex: Boolean ): String = f match {
    case All( x, t ) =>
      val op = if ( escape_latex ) "\\forall" else "all"
      "(" + op + " " + getFormulaString( x.asInstanceOf[Var], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case Ex( x, t ) =>
      val op = if ( escape_latex ) "\\exists" else "exists"
      "(" + op + " " + getFormulaString( x.asInstanceOf[Var], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case Neg( t1 ) =>
      val op = if ( escape_latex ) "\\neg" else "-"
      val str = " " + op + " " + getFormulaString( t1, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case And( t1, t2 ) =>
      val op = if ( escape_latex ) "\\land" else "&"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case Or( t1, t2 ) =>
      val op = if ( escape_latex ) "\\lor" else "|"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case Imp( t1, t2 ) =>
      val op = if ( escape_latex ) "\\rightarrow" else "->"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"

    case Var( v, _ )   => v.toString
    case Const( c, _ ) => c.toString
    case HOLAtom( f, args ) =>
      val sym = f match {
        case Const( x, _ ) => x
        case Var( x, _ )   => x
      }
      val str: String =
        if ( args.length == 2 && sym.toString.matches( """(<|>|\\leq|\\geq|=|>=|<=)""" ) ) {
          val str = getFormulaString( args( 0 ), false, escape_latex ) + " " + toLatexString.nameToLatexString( sym.toString ) + " " +
            getFormulaString( args( 1 ), false, escape_latex )
          if ( outermost ) str else "(" + str + ")"

        } else
          toLatexString.nameToLatexString( sym.toString ) + ( if ( args.isEmpty ) " " else args.map( getFormulaString( _, false, escape_latex ) ).mkString( "(", ", ", ")" ) )
      //if (outermost) str else "(" + str + ")"
      str
    case HOLFunction( f, args ) =>
      val sym = f match {
        case Const( x, _ ) => x
        case Var( x, _ )   => x
      }
      if ( args.length == 2 && sym.toString.matches( """[+\-*/]""" ) )
        "(" + getFormulaString( args( 0 ), false, escape_latex ) + " " + sym.toString + " " + getFormulaString( args( 1 ), false, escape_latex ) + ")"
      else {
        if ( args.isEmpty )
          toLatexString.nameToLatexString( sym.toString )
        else
          toLatexString.nameToLatexString( sym.toString ) + ( if ( args.isEmpty ) " " else args.map( getFormulaString( _, false, escape_latex ) ).mkString( "(", ", ", ")" ) )
      }
    // these cases need to be below the quantifiers and function/atom, since the latter are less general than abs/app
    case Abs( x, t ) =>
      "(\\lambda " + getFormulaString( x.asInstanceOf[Var], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case App( s, t ) =>
      if ( escape_latex )
        "\\apply{ " + getFormulaString( s, false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + "}"
      else
        "(@ " + getFormulaString( s, false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"

  }

  def nameToLatexString( s: String, escapebrack: Boolean = true ): String = {
    val s1 = at.logic.gapt.utils.latex.nameToLatexString( s )
    //val s2 = if (escapebrack) s1.replaceAll("\\[","(").replaceAll("\\]",")") else s1
    val s2 = if ( s == "!=" ) "\\neq" else s1
    val s3 = if ( s2 != "-" ) s2.replaceAll( "-", "" ) else s2
    s3
  }
}

