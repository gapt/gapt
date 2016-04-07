package at.logic.gapt.formats.latex

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkskNew.LKskProof.LabelledFormula

/**
 * LatexRenderer provides the user interface rendering logic for prooftool.
 */
object LatexUIRenderer {
  //TODO: merge with other exporters

  // this method is used by DrawTree when drawing projections.
  // also by ProofToLatexExporter.
  def sequentToLatexString( seq: HOLSequent ): String = {
    var s = " "
    var first = true
    for ( f <- seq.antecedent ) {
      if ( !first ) s = s + ", "
      else first = false
      s = s + formulaToLatexString( f )
    }
    s = s + " \\vdash " // \u22a2
    first = true
    for ( f <- seq.succedent ) {
      if ( !first ) s = s + ", "
      else first = false
      s = s + formulaToLatexString( f )
    }
    s
  }

  def labelledFormulaToLatexString( f: LabelledFormula ): String = formulaToLatexString( f._2 )

  def formulaToLatexString( t: LambdaExpression ): String = formulaToLatexString( t, true )

  /**
   * Converts a formula into a LaTeX interpetable string. Types are not printed.
   * @param t the lamba expression to format
   * @param outermost if set, then the expression will not be put into parenthesis. otherwise it will be, unless it is
   *                  an atom.
   * @return a string with the LaTeX coode to render t
   */
  def formulaToLatexString( t: LambdaExpression, outermost: Boolean ): String = t match {
    case Neg( f ) => """\neg """ + formulaToLatexString( f, outermost = false )
    case And( f1, f2 ) =>
      if ( outermost )
        formulaToLatexString( f1, outermost = false ) + """ \wedge """ + formulaToLatexString( f2, outermost = false )
      else
        "(" + formulaToLatexString( f1, outermost = false ) + """ \wedge """ + formulaToLatexString( f2, outermost = false ) + ")"
    case Or( f1, f2 ) =>
      if ( outermost )
        formulaToLatexString( f1, outermost = false ) + """ \vee """ + formulaToLatexString( f2, outermost = false )
      else
        "(" + formulaToLatexString( f1, outermost = false ) + """ \vee """ + formulaToLatexString( f2, outermost = false ) + ")"

    case Imp( f1, f2 ) =>
      if ( outermost )
        formulaToLatexString( f1, outermost = false ) + """ \supset """ + formulaToLatexString( f2, outermost = false )
      else
        "(" + formulaToLatexString( f1, outermost = false ) + """ \supset """ + formulaToLatexString( f2, outermost = false ) + ")"
    case Ex( v, f ) =>
      "(" + """\exists """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
    case All( v, f ) =>
      "(" + """\forall """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
    case HOLAtom( pred, args ) =>
      val name = pred match {
        case Const( n, _ ) => n
        case Var( n, _ )   => n
        case _             => throw new Exception( "An atom can only contain a const or a var on the outermost level!" )
      }
      if ( args.size == 2 && name.toString.matches( """(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)""" ) ) { //!name.toString.matches("""[\w\p{InGreek}]*""")) {
        //formats infix formulas
        if ( outermost ) {
          //if the whole formula is an infix atom, we can skip parenthesis
          formulaToLatexString( args.head, outermost = false ) + " " + UnicodeToLatex( name.toString ) + " " + formulaToLatexString( args.last, outermost = false )
        } else {
          "(" + formulaToLatexString( args.head, outermost = false ) + " " + UnicodeToLatex( name.toString ) + " " + formulaToLatexString( args.last, outermost = false ) + ")"
        }
      } else {
        //formats everything else
        UnicodeToLatex( name.toString ) + { if ( args.isEmpty ) "" else args.map( x => formulaToLatexString( x, outermost = false ) ).mkString( "(", ",", ")" ) }
      }
    case Var( name, _ )   => name
    case Const( name, _ ) => name
    case HOLFunction( f, args ) =>
      val name = f match {
        case Const( n, _ ) => n
        case Var( n, _ )   => n
        case _             => throw new Exception( "An atom can only contain a const or a var on the outermost level!" )
      }

      if ( args.size == 1 ) parseNestedUnaryFunction( name.toString, args.head, 1 )
      else if ( args.size == 2 && name.toString.matches( """(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)""" ) ) //!name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString( args.head, outermost = false ) + " " + UnicodeToLatex( name.toString ) + " " + formulaToLatexString( args.last, outermost = false ) + ")"
      else UnicodeToLatex( name.toString ) + { if ( args.isEmpty ) "" else args.map( x => formulaToLatexString( x, outermost = false ) ).mkString( "(", ",", ")" ) }
    case Abs( v, s ) => "(" + """ \lambda """ + formulaToLatexString( v, outermost = false ) + """.""" + formulaToLatexString( s, outermost = false ) + ")"
    case App( s, t ) => formulaToLatexString( s, outermost = false ) + "(" + formulaToLatexString( t, outermost = false ) + ")"
  }

  def parseNestedUnaryFunction( parent_name: String, t: LambdaExpression, n: Int ): String = t match {
    case HOLFunction( name, args ) =>
      if ( args.size == 1 && name.toString == parent_name ) parseNestedUnaryFunction( parent_name, args.head, n + 1 )
      else parent_name + { if ( n > 1 ) "^{" + n.toString + "}" else "" } + "(" + formulaToLatexString( t ) + ")"
    case _ => parent_name + { if ( n > 1 ) "^{" + n.toString + "}" else "" } + "(" + formulaToLatexString( t ) + ")"
  }

}
