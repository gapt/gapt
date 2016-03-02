package at.logic.gapt.formats.latex

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.toPrettyString
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.ceres_schema.PStructToExpressionTree.ProjectionSetSymbol
import at.logic.gapt.proofs.ceres_schema.struct.ClauseSetSymbol
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkskNew.LKskProof.LabelledFormula
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

/**
 * LatexRenderer provides the user interface rendering logic for prooftool.
 */
object LatexUIRenderer {
  //TODO: merge with other exporters

  // this method is used by DrawTree when drawing projections.
  // also by ProofToLatexExporter.
  def sequentToLatexString( seq: OccSequent ): String = {
    var s = " "
    var first = true
    for ( f <- seq.antecedent ) {
      if ( !first ) s = s + ", "
      else first = false
      s = s + formulaToLatexString( f.formula )
    }
    s = s + " \\vdash " // \u22a2
    first = true
    for ( f <- seq.succedent ) {
      if ( !first ) s = s + ", "
      else first = false
      s = s + formulaToLatexString( f.formula )
    }
    s
  }

  def formulaOccurrenceToLatexString( fo: FormulaOccurrence ): String = formulaToLatexString( fo.formula )

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
      if ( v.exptype == Tindex -> Tindex )
        "(" + """\exists^{hyp} """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
      else
        "(" + """\exists """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
    case All( v, f ) =>
      if ( v.exptype == Tindex -> Tindex )
        "(" + """\forall^{hyp} """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
      else
        "(" + """\forall """ + formulaToLatexString( v, outermost = false ) + """)""" + formulaToLatexString( f, outermost = false )
    case BigAnd( v, formula, init, end ) =>
      """ \bigwedge_{ """ + formulaToLatexString( v, outermost = false ) + "=" + formulaToLatexString( init ) + "}^{" + formulaToLatexString( end, outermost = false ) + "}" + formulaToLatexString( formula, outermost = false )

    case BigOr( v, formula, init, end ) =>
      """ \bigvee_{ """ + formulaToLatexString( v, outermost = false ) + "=" + formulaToLatexString( init, outermost = false ) + "}^{" + formulaToLatexString( end, outermost = false ) + "}" + formulaToLatexString( formula )
    case IndexedPredicate( constant, indices ) if constant != BiggerThanC =>
      {
        if ( constant.sym.isInstanceOf[ClauseSetSymbol] ) { //parse cl variables to display cut-configuration.
          val cl = constant.name.asInstanceOf[ClauseSetSymbol]
          "cl^{" + cl.name + ",(" + cl.cut_occs._1.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f, outermost = false ) ) + " | " +
            cl.cut_occs._2.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f, outermost = false ) ) + ")}"
        } else if ( constant.sym.isInstanceOf[ProjectionSetSymbol] ) { //parse pr variables to display cut-configuration.
          val pr = constant.name.asInstanceOf[ProjectionSetSymbol]
          "pr^{" + pr.name + ",(" + pr.cut_occs._1.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f, outermost = false ) ) + " | " +
            pr.cut_occs._2.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f, outermost = false ) ) + ")}"
        } //or return the predicate symbol
        else UnicodeToLatex( constant.name.toString )
      } + { if ( indices.isEmpty ) "" else indices.map( x => formulaToLatexString( x ) ).mkString( "_{", ",", "}" ) }
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
    case indexedFOVar( name, index )    => name + "_{" + formulaToLatexString( index, outermost = false ) + "}"
    case indexedOmegaVar( name, index ) => name + "_{" + formulaToLatexString( index, outermost = false ) + "}"
    case v: Var if v.sym.isInstanceOf[ClauseSetSymbol] => //Fixme: never enters here because type of ClauseSetSymbol is changed
      //parse cl variables to display cut-configuration.
      val cl = v.sym.asInstanceOf[ClauseSetSymbol]
      "cl^{" + cl.name + ",(" + cl.cut_occs._1.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f ) ) + " | " +
        cl.cut_occs._2.foldLeft( "" )( ( s, f ) => s + { if ( s != "" ) ", " else "" } + formulaToLatexString( f, outermost = false ) ) + ")}"
    case Var( name, _ ) if t.exptype == Tindex -> Tindex =>
      "\\textbf {" + name.toString + "}"
    case Var( name, _ )   => name
    case Const( name, _ ) => name
    case HOLFunction( f, args ) =>
      val name = f match {
        case Const( n, _ ) => n
        case Var( n, _ )   => n
        case _             => throw new Exception( "An atom can only contain a const or a var on the outermost level!" )
      }

      if ( name.toString == "EXP" )
        args.last.asInstanceOf[IntVar].name + "^{" + parseIntegerTerm( args.head.asInstanceOf[IntegerTerm], 0 ) + "}"
      else if ( args.size == 1 ) parseNestedUnaryFunction( name.toString, args.head, 1 )
      else if ( args.size == 2 && name.toString.matches( """(=|!=|\\neq|<|>|\\leq|\\geq|\\in|\+|-|\*|/)""" ) ) //!name.toString.matches("""[\w\p{InGreek}]*"""))
        "(" + formulaToLatexString( args.head, outermost = false ) + " " + UnicodeToLatex( name.toString ) + " " + formulaToLatexString( args.last, outermost = false ) + ")"
      else UnicodeToLatex( name.toString ) + { if ( args.isEmpty ) "" else args.map( x => formulaToLatexString( x, outermost = false ) ).mkString( "(", ",", ")" ) }
    case Abs( v, s )                           => "(" + """ \lambda """ + formulaToLatexString( v, outermost = false ) + """.""" + formulaToLatexString( s, outermost = false ) + ")"
    case App( s, t )                           => formulaToLatexString( s, outermost = false ) + "(" + formulaToLatexString( t, outermost = false ) + ")"
    case t: IntegerTerm if t.exptype == Tindex => parseIntegerTerm( t, 0 )
  }

  def parseIntegerTerm( t: IntegerTerm, n: Int ): String = t match {
    // FIXME: in the first case, we implicitly assume that all IntConsts are 0!
    // this is just done for convenience, and should be changed ASAP
    case z: IntConst => n.toString
    case IntZero()   => n.toString
    case v: IntVar if n > 0 =>
      toPrettyString( v ) + "+" + n.toString //TODO: why do we use to pretty string here? it doesn't handle LaTeX?
    case v: IntVar /* if n <= 0 */ =>
      toPrettyString( v ) //TODO: why do we use to pretty string here? it doesn't handle LaTeX?
    case Succ( s ) => parseIntegerTerm( s, n + 1 )
    case _         => throw new Exception( "Error in parseIntegerTerm(..) in gui" )
  }

  def parseNestedUnaryFunction( parent_name: String, t: LambdaExpression, n: Int ): String = t match {
    case HOLFunction( name, args ) =>
      if ( args.size == 1 && name.toString == parent_name ) parseNestedUnaryFunction( parent_name, args.head, n + 1 )
      else parent_name + { if ( n > 1 ) "^{" + n.toString + "}" else "" } + "(" + formulaToLatexString( t ) + ")"
    case _ => parent_name + { if ( n > 1 ) "^{" + n.toString + "}" else "" } + "(" + formulaToLatexString( t ) + ")"
  }

}
