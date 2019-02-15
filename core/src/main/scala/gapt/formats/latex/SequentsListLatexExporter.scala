package gapt.formats.latex

import gapt.proofs.HOLSequent
import gapt.expr._
import gapt.expr.formula.hol._
import gapt.expr.ty.->:
import gapt.expr.ty.TBase
import gapt.expr.ty.Ty

trait SequentsListLatexExporter {
  def getOutput: java.io.Writer
  def close = getOutput.close

  private val nLine = sys.props( "line.separator" )
  val smskip = nLine + nLine
  val mdskip = smskip + """\rule[-0.1cm]{5cm}{0.01cm} \\""" + smskip
  private def exportSequent( seq: HOLSequent ) = {
    if ( seq.antecedent.size > 0 ) exportTerm1( seq.antecedent.head )
    if ( seq.antecedent.size > 1 ) seq.antecedent.tail.foreach( x => { getOutput.write( smskip ); /*getOutput.write(",");*/ exportTerm1( x ) } )
    getOutput.write( smskip ); getOutput.write( """ $\vdash$ """ ); getOutput.write( smskip )
    if ( seq.succedent.size > 0 ) exportTerm1( seq.succedent.head )
    if ( seq.succedent.size > 1 ) seq.succedent.tail.foreach( x => { getOutput.write( smskip ); /*getOutput.write(",");*/ exportTerm1( x ) } )
  }

  def exportSequentList( ls: List[HOLSequent], sections: List[Tuple2[String, List[Tuple2[Any, Any]]]] ): SequentsListLatexExporter = {
    // first obtain information about the clauses, replace lambda expressions of constant type by constants (and describe it at the top of the page)
    // Also describe the types of all constants

    getOutput.write( """\documentclass[10pt, a4paper]{article}""" )
    getOutput.write( nLine )
    getOutput.write( """\""" )
    getOutput.write( """usepackage{color}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\topmargin}{-1.5cm}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\headheight}{0cm}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\headsep}{0cm}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\textheight}{1.25\textheight}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\oddsidemargin}{-1.5cm}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\evensidemargin}{-1.5cm}""" )
    getOutput.write( nLine )
    getOutput.write( """\setlength{\textwidth}{1.4\textwidth}""" )
    getOutput.write( nLine )
    getOutput.write( """\begin{document}""" )
    getOutput.write( nLine )
    sections.foreach( x => {
      getOutput.write( """\section{""" + x._1 + "}" )
      getOutput.write( nLine )
      getOutput.write( """\begin{tabular}{ll}""" )
      x._2.foreach( y => {
        printOnMatch( y._1 )
        getOutput.write( " & " )
        printOnMatch( y._2 )
        getOutput.write( """ \\ """ )
        getOutput.write( nLine )
      } )
      getOutput.write( """\end{tabular}""" )
      getOutput.write( nLine )
    } )
    getOutput.write( """\section{Clauses}""" )
    getOutput.write( nLine )
    ls.foreach( x => { exportSequent( x ); getOutput.write( mdskip ) } )
    printTypes( ls )
    getOutput.write( """\end{document}""" )
    this
  }

  private def getFSVars( fs: HOLSequent ): Set[Var] = fs.formulas.toSet.flatMap( getVars )
  private def getVars( l: Expr ): Set[Var] = l match {
    case v: Var      => Set( v )
    case c: Const    => Set()
    case Abs( x, t ) => getVars( t ) ++ getVars( x )
    case App( s, t ) => getVars( s ) ++ getVars( t )
  }

  private def getFSConsts( fs: HOLSequent ): Set[Const] = fs.formulas.toSet.flatMap( getConsts )
  private def getConsts( l: Expr ): Set[Const] = l match {
    case v: Var      => Set()
    case c: Const    => Set( c )
    case Abs( x, t ) => getConsts( t ) ++ getConsts( x )
    case App( s, t ) => getConsts( s ) ++ getConsts( t )
  }

  def printTypes( l: List[HOLSequent] ) = {
    val ( vmap, cmap ) = getTypes( l )
    getOutput.write( "\\subsection{Variable Types}" + nLine )

    getOutput.write( "\\[\\begin{array}{ll}" + nLine )
    for ( ( key, set ) <- vmap.toList.sortBy( _._1 )( TAOrdering ) ) {
      var set_ = set.toList.sorted
      while ( set_.nonEmpty ) {
        val ( ten, rest ) = set_.splitAt( 10 )
        getOutput.write( ten.mkString( "", ", ", " & " ) + typeToString( key ) )
        getOutput.write( " \\\\" + nLine )
        set_ = rest
      }
    }
    getOutput.write( """\end{array}\]""" )

    getOutput.write( "\\subsection{Constant Types}" + nLine )
    getOutput.write( "\\[\\begin{array}{ll}" + nLine )
    for ( ( key, set ) <- cmap.toList.sortBy( _._1 )( TAOrdering ) ) {
      var set_ = set.toList.sorted
      while ( set_.nonEmpty ) {
        val ( ten, rest ) = set_.splitAt( 10 )
        getOutput.write( ten.mkString( "", ", ", " & " ) + typeToString( key ) )
        getOutput.write( " \\\\" + nLine )
        set_ = rest
      }
    }
    getOutput.write( """\end{array}\]""" )
  }

  def typeToString( t: Ty, outermost: Boolean = true ): String = t match {
    case TBase( name, _ ) => name
    case t1 ->: t2 =>
      typeToString_( t1 ) +
        " > " +
        typeToString_( t2 )
  }

  def typeToString_( t: Ty ): String = t match {
    case TBase( name, _ ) => name
    case t1 ->: t2 =>
      ( "(" ) +
        typeToString_( t1 ) +
        " > " +
        typeToString_( t2 ) +
        ")"
  }

  private def getTypes( l: List[HOLSequent] ) = {
    val vars = l.foldLeft( Set[Var]() )( ( acc, fs ) => acc ++ getFSVars( fs ) )
    val consts = l.foldLeft( Set[Const]() )( ( acc, fs ) => acc ++ getFSConsts( fs ) )
    val svars = vars.map( _.name.toString() )
    val cvars = consts.map( _.name.toString() )
    if ( cvars.exists( svars.contains( _ ) ) || svars.exists( cvars.contains( _ ) ) )
      println( "WARNING: exported const and varset are not disjunct!" )

    val varmap = vars.foldLeft( Map[Ty, Set[String]]() )( ( map, v ) => {
      if ( map contains v.ty ) {
        val nset = map( v.ty ) + v.name.toString()
        map + ( ( v.ty, nset ) )
      } else {
        map + ( ( v.ty, Set( v.name.toString() ) ) )
      }
    } )
    val constmap = consts.foldLeft( Map[Ty, Set[String]]() )( ( map, v ) => {
      if ( map contains v.ty ) {
        val nset = map( v.ty ) + v.name.toString()
        map + ( ( v.ty, nset ) )
      } else {
        map + ( ( v.ty, Set( v.name.toString() ) ) )
      }
    } )

    ( varmap, constmap )
  }

  private def printOnMatch( a: Any ) = a match {
    case le: Expr => exportTerm1( le )
    case ta: Ty   => getOutput.write( "$" + LatexExporter( ta ) + "$" )
    case _        => getOutput.write( a.toString )
  }

  private def exportTerm1( f: Expr ) = {
    getOutput.write( "$" )
    LatexExporter( f )
    getOutput.write( "$" )
  }
  /*private def replaceTerm(f: Expr, defs: Map[Int, Tuple2[Abs,Var]]): Expr = f match {
    case v: Var => v
    case App(a,b) => App(replaceTerm(a, defs), replaceTerm(b, defs))
    case a @ Abs(x,b) => defs.get(extractAbs(a.asInstanceOf[Abs])) match {
      case Some(v) => v._2
      case _ => Abs(x, replaceTerm(b, defs))
    }
  }*/
}
