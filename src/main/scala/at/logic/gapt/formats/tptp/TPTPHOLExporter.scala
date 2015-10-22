package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lk.base.LKProof

/**
 * Created by marty on 12/10/13.
 */
object TPTPHOLExporter extends TPTPHOLExporter
class TPTPHOLExporter {
  /**
   * Exports the given FSequent list to the THF fragment of TPTP. The default behavior of the exporter
   * expects a sequent list in a negative context, i.e. it will encode the refutation of the arguments.
   *
   * @note In contrast to prover9, for multiple conjectures, each of them has to be proved.
   */
  val nLine = sys.props( "line.separator" )

  def apply( l: List[HOLSequent], positive: Boolean = false ): String = {
    require( l.nonEmpty, "Cannot export an empty sequent list!" )
    val ( vs, vnames, cs, cnames ) = createNamesFromSequent( l )

    var index = 0
    val vdecs_ = for ( v <- vs ) yield {
      index = index + 1
      thf_type_dec( index, v, vnames ) + nLine
    }

    val vdecs = vdecs_.foldLeft( "" )( _ ++ _ )

    val cdecs_ = for ( c <- cs if c.name != "=" ) yield {
      index = index + 1
      thf_type_dec( index, c, cnames ) + nLine
    }
    val cdecs = cdecs_.foldLeft( "" )( _ ++ _ )

    val sdecs = positive match {
      case true =>
        for ( fs <- l ) yield {
          index = index + 1
          //thf_sequent_dec( index, fs, vnames, cnames ) + nLine //leo doesn't support sequents?
          thf_formula_dec( index, fs.toImplication, vnames, cnames ) + nLine
        }
      case false =>
        val negClauses = Neg( And( l.map( closedFormula ) ) )
        index = index + 1
        // since in thf conjectures are seen as conjunction. the negated cnf is one big formula
        List( thf_formula_dec( index, negClauses, vnames, cnames ) )

    }

    //"% variable type declarations" + nLine + vdecs +
    "% constant type declarations" + nLine + cdecs +
      "% sequents" + nLine + sdecs.foldLeft( "" )( ( s, x ) => s + x + nLine )

  }

  def printStatistics( vnames: NameMap, cnames: CNameMap ): Unit = {
    if ( cnames.isEmpty && vnames.isEmpty ) {
      println( "% No symbol translation necessary!" )
      return ()
    };
    println( "% Symbol translation table for THF export:" )
    val csyms = cnames.keySet.toList.map( { case Const( s, _ ) => s } )
    val vsyms = vnames.keySet.toList.map( { case Var( s, _ ) => s } )

    val width = ( vsyms ++ csyms ).sortWith( ( x, y ) => y.size < x.size ).head.size

    for ( ( c, s ) <- cnames ) {
      val sym = c.sym.toString
      if ( sym != s ) {
        print( "%   " )
        print( sym )
        for ( i <- sym.size to ( width + 1 ) ) print( " " )
        print( " -> " )
        print( s )
        println()
      }
    }

    val cunchanged = for ( ( c, s ) <- cnames; if ( c.sym.toString == s ) ) yield { s }
    if ( cunchanged.nonEmpty ) println( "% Unchanged constants: " + cunchanged.mkString( "," ) )

    println( "% " )

    for ( ( c, s ) <- vnames ) {
      val sym = c.sym.toString
      if ( sym != s ) {
        print( "%   " )
        print( sym )
        for ( i <- sym.size to ( width + 1 ) ) print( " " )
        print( " -> " )
        print( s )
        println()
      }
    }

    val vunchanged = for ( ( c, s ) <- vnames; if ( c.sym.toString == s ) ) yield { s }
    if ( vunchanged.nonEmpty ) println( "% Unchanged variables: " + vunchanged.mkString( "," ) )

  }

  type NameMap = Map[Var, String]
  val emptyNameMap = Map[Var, String]()
  type CNameMap = Map[Const, String]
  val emptyCNameMap = Map[Const, String]()

  def createFormula( f: LambdaExpression, map: Map[Var, String] ) = f match {
    case Var( _, _ ) => map( f.asInstanceOf[Var] )
  }

  def createNamesFromSequent( l: List[HOLSequent] ): ( List[Var], NameMap, List[Const], CNameMap ) = {
    val vs = l.foldLeft( Set[Var]() )( ( set, fs ) => getVars( fs.toFormula, set ) ).toList
    val cs = l.foldLeft( Set[Const]() )( ( set, fs ) => getConsts( fs.toFormula, set ) ).toList
    ( vs, createNamesFromVar( vs ), cs, createNamesFromConst( cs ) )
  }

  def createNamesFromVar( l: List[Var] ): NameMap = l.foldLeft( emptyNameMap )( ( map, v ) => {
    if ( map contains v )
      map
    else {
      val name = mkVarName( v.name.toString(), map )
      map + ( ( v, name ) )
    }
  } )

  def closedFormula( fs: HOLSequent ): HOLFormula = univclosure( fs.toFormula )

  def createNamesFromConst( l: List[Const] ): CNameMap = l.foldLeft( emptyCNameMap )( ( map, v ) => {
    if ( map contains v )
      map
    else {
      val name = mkConstName( v.name.toString(), map )
      map + ( ( v, name ) )
    }
  } )

  def thf_sequent_dec( i: Int, f: HOLSequent, vmap: NameMap, cmap: CNameMap ) = {
    "thf(" + i + ", conjecture, [" +
      ( f.antecedent.map( f => thf_formula( f, vmap, cmap ) ).mkString( "," ) ) +
      "] --> [" +
      ( f.succedent.map( f => thf_formula( f, vmap, cmap ) ).mkString( "," ) ) +
      "] )."
  }

  def thf_formula_dec( i: Int, f: HOLFormula, vmap: NameMap, cmap: CNameMap ) = {
    "thf(" + i + ", conjecture, " + thf_formula( f, vmap, cmap, true ) + " )."
  }

  def thf_negformula_dec( i: Int, f: HOLFormula, vmap: NameMap, cmap: CNameMap ) = {
    "thf(" + i + ", negated_conjecture, " + thf_formula( f, vmap, cmap, true ) + " )."
  }

  private def addparens( str: String, cond: Boolean ) = if ( cond ) "(" + str + ")" else str
  def thf_formula( f: LambdaExpression, vmap: NameMap, cmap: CNameMap, outermost: Boolean = false ): String = {
    f match {
      case Top()                      => "$true"
      case Bottom()                   => "$false"
      case Neg( x )                   => addparens( " ~(" + thf_formula( x, vmap, cmap ) + ")", outermost ) //negation of atoms needs parenthesis!
      case And( x, y )                => addparens( thf_formula( x, vmap, cmap ) + " & " + thf_formula( y, vmap, cmap ), !outermost )
      case Or( x, y )                 => addparens( thf_formula( x, vmap, cmap ) + " | " + thf_formula( y, vmap, cmap ), !outermost )
      case Imp( x, y )                => addparens( thf_formula( x, vmap, cmap ) + " => " + thf_formula( y, vmap, cmap ), !outermost )
      case All( x, t )                => addparens( "![" + vmap( x ) + " : " + getTypeString( x.exptype ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case Ex( x, t )                 => addparens( "?[" + vmap( x ) + " : " + getTypeString( x.exptype ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case Eq( x, y )                 => addparens( thf_formula( x, vmap, cmap ) + " = " + thf_formula( y, vmap, cmap ), !outermost )
      case Abs( x, t )                => addparens( "^[" + vmap( x ) + " : " + getTypeString( x.exptype ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case App( s, t )                => addparens( thf_formula( s, vmap, cmap ) + " @ " + thf_formula( t, vmap, cmap ), !outermost )
      case Var( _, _ )                => vmap( f.asInstanceOf[Var] )
      case NonLogicalConstant( _, _ ) => cmap( f.asInstanceOf[Const] )
      case _                          => throw new Exception( "TPTP export does not support outermost connective of " + f )
    }
  }

  def thf_type_dec( i: Int, v: Var, vmap: NameMap ): String = {
    require( vmap.contains( v ), "Did not generate an export name for " + v + "!" )
    "thf(" + i + ", type, " + vmap( v ) + ": " + getTypeString( v.exptype ) + " )."
  }

  def thf_type_dec( i: Int, c: Const, cmap: CNameMap ): String = {
    require( cmap.contains( c ), "Did not generate an export name for " + c + "!" )
    "thf(" + i + ", type, " + cmap( c ) + ": " + getTypeString( c.exptype ) + " )."
  }

  def getTypeString( t: Ty ): String = getTypeString( t, true )
  def getTypeString( t: Ty, outer: Boolean ): String = t match {
    case Ti                => "$i"
    case To                => "$o"
    case t1 -> t2 if outer => getTypeString( t1, false ) + " > " + getTypeString( t2, false )
    case t1 -> t2          => "(" + getTypeString( t1, false ) + " > " + getTypeString( t2, false ) + ")"
    case _                 => throw new Exception( "TPTP type export for " + t + " not implemented!" )
  }

  def mkVarName( str: String, map: Map[Var, String] ) = {
    val fstr_ = str.filter( _.toString.matches( "[a-zA-Z0-9]" ) )
    val fstr = if ( fstr_.isEmpty ) {
      println( "Warning: " + str + " needs to be completely replaced by a fresh variable!" )
      "V"
    } else fstr_
    val prefix = if ( fstr.head.isDigit ) "X" + fstr
    else fstr.head.toUpper + fstr.tail
    val values = map.toList.map( _._2 )
    if ( values contains prefix )
      appendPostfix( prefix, values )
    else
      prefix
  }

  def mkConstName( str: String, map: CNameMap ) = {
    val fstr_ = str match {
      case "=" => "=" //equality is handled explicitly
      case "+" => "plus"
      case "-" => "minus"
      case "*" => "times"
      case "/" => "div"
      case "<" => "lt"
      case ">" => "gt"
      case _   => str.filter( _.toString.matches( "[a-zA-Z0-9]" ) )
    }
    val fstr = if ( fstr_.isEmpty ) {
      println( "Warning: " + str + " needs to be completely replaced by a fresh constant!" )
      "c"
    } else fstr_
    val prefix = if ( fstr.head.isDigit ) "c" + fstr
    else fstr.head.toLower + fstr.tail
    val values = map.toList.map( _._2 )
    if ( values contains prefix )
      appendPostfix( prefix, values )
    else
      prefix
  }

  def appendPostfix( str: String, l: List[String] ) = {
    var i = 100
    while ( l contains ( str + i ) ) {
      i = i + 1
    }
    str + i
  }

  /** extract all variables, bound and free */
  def getVars( t: LambdaExpression, set: Set[Var] ): Set[Var] = t match {
    case Const( _, _ ) => set
    case Var( _, _ )   => set + t.asInstanceOf[Var]
    case App( s, t )   => getVars( s, getVars( t, set ) )
    case Abs( x, t )   => getVars( t, set + x )
  }

  def getConsts( t: LambdaExpression, set: Set[Const] ): Set[Const] = t match {
    case EqC( _ )                   => set
    case _: LogicalConstant         => set
    case NonLogicalConstant( _, _ ) => set + t.asInstanceOf[Const]
    case Var( _, _ )                => set
    case App( s, t )                => getConsts( s, getConsts( t, set ) )
    case Abs( x, t )                => getConsts( t, set )
  }

}
