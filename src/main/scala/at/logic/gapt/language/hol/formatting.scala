package at.logic.gapt.language.hol

import at.logic.gapt.language.hol.logicSymbols._

/**
 * Created by marty on 4/16/15.
 */

/**
 * Formats a HOL expression without types and the outermost parenthesis. Conjunction, disjunction and implication
 * are considered right associative, i.e. a /\ ((b /\ c) /\ d) = a /\ (b /\ c) /\ d. Equation is rendered infix.
 */
object toPrettyString {
  def apply( e: HOLExpression ) = string_of_expr( e, false )

  //TODO: introduce binding priorities of and over or.
  def string_of_expr( e: HOLExpression, use_parens: Boolean = false ): String = e match {
    case HOLVar( x, tpe )   => x.toString
    case HOLConst( x, tpe ) => x.toString
    case HOLAtom( c: HOLConst, List( left, right ) ) if c.sym == EqSymbol =>
      string_of_expr( left, true ) + " " + EqSymbol + " " + string_of_expr( right, true )
    case HOLAtom( x, Nil ) => string_of_expr( x, false )
    case HOLAtom( x, args ) =>
      string_of_expr( x, false ) + args.map( x => string_of_expr( x, true ) ).mkString( "(", ", ", ")" )
    case HOLFunction( x, Nil, tpe ) => string_of_expr( x, false )
    case HOLFunction( x, args, tpe ) =>
      string_of_expr( x, false ) + args.map( x => string_of_expr( x, true ) ).mkString( "(", ", ", ")" )
    // right-assoc operators: and, or, imp
    case HOLAnd( x, y @ HOLAnd( _, _ ) ) => opt_parens( string_of_expr( x, true ) + AndSymbol + string_of_expr( y, false ), use_parens )
    case HOLOr( x, y @ HOLOr( _, _ ) )   => opt_parens( string_of_expr( x, true ) + OrSymbol + string_of_expr( y, true ), use_parens )
    case HOLImp( x, y @ HOLImp( _, _ ) ) => opt_parens( string_of_expr( x, true ) + ImpSymbol + string_of_expr( y, true ), use_parens )
    // no parens for double negation
    case HOLNeg( x @ HOLNeg( _ ) )       => NegSymbol + opt_parens( string_of_expr( x, false ), use_parens )
    // default case
    case HOLAnd( x, y )                  => opt_parens( string_of_expr( x, true ) + AndSymbol + string_of_expr( y, true ), use_parens )
    case HOLEquation( x, y )             => opt_parens( string_of_expr( x, true ) + EqSymbol + string_of_expr( y, true ), use_parens )
    case HOLOr( x, y )                   => opt_parens( string_of_expr( x, true ) + OrSymbol + string_of_expr( y, true ), use_parens )
    case HOLImp( x, y )                  => opt_parens( string_of_expr( x, true ) + ImpSymbol + string_of_expr( y, true ), use_parens )
    case HOLNeg( x )                     => NegSymbol + opt_parens( string_of_expr( x, true ), use_parens )
    case HOLExVar( x, f )                => opt_parens( ExistsSymbol + string_of_expr( x, false ) + "." + string_of_expr( f, true ), use_parens )
    case HOLAllVar( x, f )               => opt_parens( ForallSymbol + string_of_expr( x, false ) + "." + string_of_expr( f, true ), use_parens )
    case HOLAbs( v, exp )                => opt_parens( "λ" + string_of_expr( v ) + "." + string_of_expr( exp, true ), use_parens )
    case HOLApp( l, r )                  => opt_parens( string_of_expr( l, true ) + " " + string_of_expr( r, true ), use_parens )
    case _                               => throw new Exception( "Unrecognized symbol." )
  }

  def opt_parens( str: String, use_parens: Boolean ) = if ( use_parens ) "(" + str + ")" else str
}

/**
 * This is a prover9 style formatting which can be parsed by LLK.
 */
object toLLKString {
  def apply( e: HOLExpression ) = toLatexString.getFormulaString( e, true, false )
}

/**
 * This is a Latex formatting which can be parsed by LLK.
 */
object toLatexString {
  def apply( e: HOLExpression ) = getFormulaString( e, true, true )

  def getFormulaString( f: HOLExpression, outermost: Boolean = true, escape_latex: Boolean ): String = f match {
    case HOLAllVar( x, t ) =>
      val op = if ( escape_latex ) "\\forall" else "all"
      "(" + op + " " + getFormulaString( x.asInstanceOf[HOLVar], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case HOLExVar( x, t ) =>
      val op = if ( escape_latex ) "\\exists" else "exists"
      "(" + op + " " + getFormulaString( x.asInstanceOf[HOLVar], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case HOLNeg( t1 ) =>
      val op = if ( escape_latex ) "\\neg" else "-"
      val str = " " + op + " " + getFormulaString( t1, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case HOLAnd( t1, t2 ) =>
      val op = if ( escape_latex ) "\\land" else "&"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case HOLOr( t1, t2 ) =>
      val op = if ( escape_latex ) "\\lor" else "|"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"
    case HOLImp( t1, t2 ) =>
      val op = if ( escape_latex ) "\\rightarrow" else "->"
      val str = getFormulaString( t1, false, escape_latex ) + " " + op + " " + getFormulaString( t2, false, escape_latex )
      if ( outermost ) str else "(" + str + ")"

    case HOLAtom( f, args ) =>
      val sym = f match {
        case HOLConst( x, _ ) => x
        case HOLVar( x, _ )   => x
      }
      val str: String =
        if ( args.length == 2 && sym.toString.matches( """(<|>|\\leq|\\geq|=|>=|<=)""" ) ) {
          val str = getFormulaString( args( 0 ), false, escape_latex ) + " " + nameToLatexString( sym.toString ) + " " +
            getFormulaString( args( 1 ), false, escape_latex )
          if ( outermost ) str else "(" + str + ")"

        } else
          nameToLatexString( sym.toString ) + ( if ( args.isEmpty ) " " else args.map( getFormulaString( _, false, escape_latex ) ).mkString( "(", ", ", ")" ) )
      //if (outermost) str else "(" + str + ")"
      str
    case HOLFunction( f, args, _ ) =>
      val sym = f match {
        case HOLConst( x, _ ) => x
        case HOLVar( x, _ )   => x
      }
      if ( args.length == 2 && sym.toString.matches( """[+\-*/]""" ) )
        "(" + getFormulaString( args( 0 ), false, escape_latex ) + " " + sym.toString + " " + getFormulaString( args( 1 ), false, escape_latex ) + ")"
      else {
        if ( args.isEmpty )
          nameToLatexString( sym.toString )
        else
          nameToLatexString( sym.toString ) + ( if ( args.isEmpty ) " " else args.map( getFormulaString( _, false, escape_latex ) ).mkString( "(", ", ", ")" ) )
      }

    case HOLVar( v, _ )   => v.toString
    case HOLConst( c, _ ) => c.toString
    case HOLAbs( x, t ) =>
      "(\\lambda " + getFormulaString( x.asInstanceOf[HOLVar], false, escape_latex ) + " " + getFormulaString( t, false, escape_latex ) + ")"
    case HOLApp( s, t ) =>
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

