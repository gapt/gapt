package at.logic.gapt.formats.tptp

import ammonite.ops._

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.replaceAbstractions
import at.logic.gapt.expr.hol._
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.{ ETAnd, ETAtom, ETTop, ExpansionProof, ExpansionSequent, ExpansionTree }
import at.logic.gapt.provers.groundFreeVariables

sealed class TPTPFormulaRole
case object TPTPAxiom extends TPTPFormulaRole { override def toString() = "axiom" }
case object TPTPDefinition extends TPTPFormulaRole { override def toString() = "definition" }
case object TPTPConjecture extends TPTPFormulaRole { override def toString() = "conjecture" }
case object TPTPNegatedConjecture extends TPTPFormulaRole { override def toString() = "negated_conjecture" }

object TPTPHOLExporter extends TPTPHOLExporter

class TPTPHOLExporter {
  /**
   * Exports the given FSequent list to the THF fragment of TPTP. The default behavior of the exporter
   * expects a sequent list in a negative context, i.e. it will encode the refutation of the arguments.
   *
   * @note In contrast to prover9, for multiple conjectures, each of them has to be proved.
   */
  private val nLine = sys.props( "line.separator" )

  /**
   * Exports a sequent set as TPTP thf problem to prove unsatisfiability
   *
   * @param ls the list of sequents to export
   * @param filename the filename
   */
  def apply( ls: List[HOLSequent], filename: String ) =
    write( Path( filename, pwd ), export_negative( ls ) )

  /**
   * Exports a sequent as TPTP thf problem to prove validity
   *
   * @param seq the sequent to export
   * @param filename the filename
   */
  def apply( seq: HOLSequent, filename: String, separate_axioms: Boolean = false ) =
    write( Path( filename, pwd ), export_positive( seq, separate_axioms ) )

  /**
   * Exports an expansion proof as TPTP thf problem to prove validity
   *
   * @param seq the sequent to export
   * @param filename the filename
   * @param maximize_axiom_declarations if true, all conjunctions
   * @param lambda_lifting apply lambda lifting to deep formula and add the definitions into to the antecedent of the formula
   */
  def apply( seq: ExpansionSequent, filename: String,
             maximize_axiom_declarations: Boolean, lambda_lifting: Boolean ) =
    write( Path( filename, pwd ), export( seq, maximize_axiom_declarations, lambda_lifting ) )

  /**
   * Exports an expansion proof as TPTP thf problem. The antedent of the
   *
   * @param ep the expansion proof to export
   * @param maximize_axiom_declarations if true, all conjunctions
   * @param lambda_lifting apply lambda lifting to deep formula and add the definitions into to the antecedent of the formula
   */
  def export( ep: ExpansionSequent, maximize_axiom_declarations: Boolean = true, lambda_lifting: Boolean = false ): String = {
    val ep1 = if ( maximize_axiom_declarations ) simplify_antecedent( ep ) else ep
    val es1: HOLSequent = if ( lambda_lifting ) lambda_lift_and_add_definitions( ep1.deep ) else ep1.deep
    val ( es2, _ ) = groundFreeVariables( es1 )
    val es3 = if ( maximize_axiom_declarations ) simplify_antecedent2( es2 ) else es2 //the deep conversion in the antecedent also introduces conjunctions
    val es4 = es3.map( simplify.apply ) //remove top / bottom if possible
    export_positive( es4, maximize_axiom_declarations )
  }

  /**
   * Exports a sequent set as TPTP thf problem to prove unsatisfiability
   *
   * @param ls the list of sequents to export
   */
  def export_negative( ls: List[HOLSequent] ): String = {
    require( ls.nonEmpty, "Cannot export an empty sequent list!" )
    val ( vs, vnames, cs, cnames ) = createNamesFromSequent( ls )

    var index = 0

    val types = for ( seq <- ls; f <- seq.elements; st <- subTerms( f ); t <- baseTypes( st.ty ) ) yield t
    val tdecls = for ( t <- types.distinct if t != Ti && t != To ) yield { index += 1; s"thf($index, type, $t: $$tType).$nLine" }

    val cdecs_ = for ( c <- cs if c.name != "=" ) yield {
      index = index + 1
      thf_type_dec( index, c, cnames ) + nLine
    }
    val cdecs = cdecs_.mkString

    val sdecs = {
      val negClauses = Neg( And( ls.map( closedFormula ) ) )
      index = index + 1
      // since in thf conjectures are seen as conjunction. the negated cnf is one big formula
      List( thf_formula_dec( index, negClauses, TPTPConjecture, vnames, cnames ) )
    }

    s"% type declarations$nLine" + tdecls.mkString +
      //"% variable type declarations" + nLine + vdecs +
      "% constant type declarations" + nLine + cdecs +
      "% sequents" + nLine + sdecs.foldLeft( "" )( ( s, x ) => s + x + nLine )

  }

  /**
   * Exports a sequent as TPTP thf problem to prove validity
   *
   * @param seq the sequent to be proved valid
   */
  def export_positive( seq: HOLSequent, separate_axioms: Boolean = false ): String = {
    require( freeVariables( seq ).isEmpty, "Can only export ground positive sequent sets!" )
    val ( vs, vnames, cs, cnames ) = createNamesFromSequent( seq :: Nil )

    var index = 0

    val types = for ( f <- seq.elements; st <- subTerms( f ); t <- baseTypes( st.ty ) ) yield t
    val tdecls = for ( t <- types.distinct if t != Ti && t != To ) yield {
      index += 1; s"thf($index, type, $t: $$tType).$nLine"
    }

    val cdecs_ = for ( c <- cs if c.name != "=" ) yield {
      index = index + 1
      thf_type_dec( index, c, cnames ) + nLine
    }
    val cdecs = cdecs_.mkString

    val sdecs = separate_axioms match {
      case true =>
        val axioms = seq.antecedent
        val goal = Or( seq.succedent ) // work around different ATP's interpretations of multiple conclusions
        val axiom_decs =
          for ( fs <- axioms ) yield {
            index = index + 1
            thf_formula_dec( index, fs, TPTPAxiom, vnames, cnames )
          }
        ( axiom_decs.foldLeft( "" )( ( s, x ) => s + x + nLine )
          + thf_formula_dec( index + 1, goal, TPTPConjecture, vnames, cnames ) )
      case false =>
        thf_formula_dec( index + 1, seq.toImplication, TPTPConjecture, vnames, cnames )
    }

    "% type declarations" + nLine + tdecls.mkString +
      "% constant type declarations" + nLine + cdecs +
      "% sequents" + nLine + sdecs
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
      val sym = c.name
      if ( sym != s ) {
        print( "%   " )
        print( sym )
        for ( i <- sym.size to ( width + 1 ) ) print( " " )
        print( " -> " )
        print( s )
        println()
      }
    }

    val cunchanged = for ( ( c, s ) <- cnames; if ( c.name == s ) ) yield { s }
    if ( cunchanged.nonEmpty ) println( "% Unchanged constants: " + cunchanged.mkString( "," ) )

    println( "% " )

    for ( ( c, s ) <- vnames ) {
      val sym = c.name
      if ( sym != s ) {
        print( "%   " )
        print( sym )
        for ( i <- sym.size to ( width + 1 ) ) print( " " )
        print( " -> " )
        print( s )
        println()
      }
    }

    val vunchanged = for ( ( c, s ) <- vnames; if ( c.name == s ) ) yield { s }
    if ( vunchanged.nonEmpty ) println( "% Unchanged variables: " + vunchanged.mkString( "," ) )

  }

  type NameMap = Map[Var, String]
  val emptyNameMap = Map[Var, String]()
  type CNameMap = Map[Const, String]
  val emptyCNameMap = Map[Const, String]()

  def createFormula( f: Expr, map: Map[Var, String] ) = f match {
    case Var( _, _ ) => map( f.asInstanceOf[Var] )
  }

  def createNamesFromSequent( l: List[HOLSequent] ): ( List[Var], NameMap, List[Const], CNameMap ) = {
    val vs = l.foldLeft( Set[Var]() )( ( set, fs ) => getVars( fs.toDisjunction, set ) ).toList
    val cs = l.foldLeft( Set[Const]() )( ( set, fs ) => getConsts( fs.toDisjunction, set ) ).toList
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

  def closedFormula( fs: HOLSequent ): Formula = universalClosure( fs.toDisjunction )

  def createNamesFromConst( l: List[Const] ): CNameMap = l.foldLeft( emptyCNameMap )( ( map, v ) => {
    if ( map contains v )
      map
    else {
      val name = mkConstName( v.name.toString(), map )
      map + ( ( v, name ) )
    }
  } )

  def thf_formula_dec( i: Int, f: Formula, role: TPTPFormulaRole, vmap: NameMap, cmap: CNameMap ): String = {
    val f_str = thf_formula( f, vmap, cmap, true )
    val internal_str = f.toString.flatMap( { case '\n' => "\n% "; case x => x :: Nil } ) //add comment after newline
    s"${nLine}% formula: $internal_str ${nLine}thf(${i}, ${role}, ${f_str} )."
  }

  private def addparens( str: String, cond: Boolean ) = if ( cond ) "(" + str + ")" else str
  def thf_formula( f: Expr, vmap: NameMap, cmap: CNameMap, outermost: Boolean = false ): String = {
    f match {
      case Top()                      => "$true"
      case Bottom()                   => "$false"
      case Neg( x )                   => addparens( " ~(" + thf_formula( x, vmap, cmap ) + ")", outermost ) //negation of atoms needs parenthesis!
      case And( x, y )                => addparens( thf_formula( x, vmap, cmap ) + " & " + thf_formula( y, vmap, cmap ), !outermost )
      case Or( x, y )                 => addparens( thf_formula( x, vmap, cmap ) + " | " + thf_formula( y, vmap, cmap ), !outermost )
      case Imp( x, y )                => addparens( thf_formula( x, vmap, cmap ) + " => " + thf_formula( y, vmap, cmap ), !outermost )
      case All( x, t )                => addparens( "![" + vmap( x ) + " : " + getTypeString( x.ty ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case Ex( x, t )                 => addparens( "?[" + vmap( x ) + " : " + getTypeString( x.ty ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case Eq( x, y )                 => addparens( thf_formula( x, vmap, cmap ) + " = " + thf_formula( y, vmap, cmap ), !outermost )
      case Abs( x, t )                => addparens( "^[" + vmap( x ) + " : " + getTypeString( x.ty ) + "] : (" + thf_formula( t, vmap, cmap ) + ")", !outermost )
      case App( s, t )                => addparens( thf_formula( s, vmap, cmap ) + " @ " + thf_formula( t, vmap, cmap ), !outermost )
      case Var( _, _ )                => vmap( f.asInstanceOf[Var] )
      case NonLogicalConstant( _, _ ) => cmap( f.asInstanceOf[Const] )
      case _                          => throw new Exception( "TPTP export does not support outermost connective of " + f )
    }
  }

  def thf_type_dec( i: Int, v: Var, vmap: NameMap ): String = {
    require( vmap.contains( v ), "Did not generate an export name for " + v + "!" )
    "thf(" + i + ", type, " + vmap( v ) + ": " + getTypeString( v.ty ) + " )."
  }

  def thf_type_dec( i: Int, c: Const, cmap: CNameMap ): String = {
    require( cmap.contains( c ), "Did not generate an export name for " + c + "!" )
    "thf(" + i + ", type, " + cmap( c ) + ": " + getTypeString( c.ty ) + " )."
  }

  def getTypeString( t: Ty ): String = getTypeString( t, true )
  def getTypeString( t: Ty, outer: Boolean ): String = t match {
    case Ti                 => "$i"
    case To                 => "$o"
    case TBase( name, Nil ) => name
    case t1 -> t2 if outer  => getTypeString( t1, false ) + " > " + getTypeString( t2, false )
    case t1 -> t2           => "(" + getTypeString( t1, false ) + " > " + getTypeString( t2, false ) + ")"
    case _                  => throw new Exception( "TPTP type export for " + t + " not implemented!" )
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
  def getVars( t: Expr, set: Set[Var] ): Set[Var] = t match {
    case Const( _, _ ) => set
    case Var( _, _ )   => set + t.asInstanceOf[Var]
    case App( s, t )   => getVars( s, getVars( t, set ) )
    case Abs( x, t )   => getVars( t, set + x )
  }

  def getConsts( t: Expr, set: Set[Const] ): Set[Const] = t match {
    case EqC( _ )                   => set
    case _: LogicalConstant         => set
    case NonLogicalConstant( _, _ ) => set + t.asInstanceOf[Const]
    case Var( _, _ )                => set
    case App( s, t )                => getConsts( s, getConsts( t, set ) )
    case Abs( x, t )                => getConsts( t, set )
  }

  def simplify_antecedent( es: ExpansionSequent ): ExpansionSequent = {
    es.antecedent.flatMap( {
      case ETAnd( e1, e2 ) => List( e1, e2 )
      case e               => List( e )
    } ) match {
      case ant if ant == es.antecedent => es
      case ant /* ant !- es.antecedent */ =>
        val ant0 = ant.filterNot( _.deep == Top() )
        val et = Sequent( ant0, es.succedent )
        simplify_antecedent( et )
    }
  }

  def simplify_antecedent2( es: HOLSequent ): HOLSequent = {
    es.antecedent.flatMap( {
      case And( e1, e2 ) => List( e1, e2 )
      case e             => List( e )
    } ) match {
      case ant if ant == es.antecedent => es
      case ant /* ant !- es.antecedent */ =>
        val ant0 = ant.filterNot( _ == Top() )
        val et = Sequent( ant0, es.succedent )
        simplify_antecedent2( et )
    }
  }

  def strip_lambdas( e: Expr, context: List[Var] ): ( Expr, List[Var] ) =
    e match {
      case Abs( v, t ) => strip_lambdas( t, v :: context )
      case t           => ( t, context.reverse )
    }

  def lambda_lift_and_add_definitions( seq: HOLSequent ): HOLSequent = {
    val ( cmap, seq0 :: Nil ) = replaceAbstractions( seq :: Nil )
    val qaxioms: Seq[Formula] = cmap.toSeq.map {
      case ( term_, name ) => {
        //term_ should be closed, but to be sure we add the free variables the variables stripped from the outer-most
        //lambda-block in term_
        val fv = freeVariables( term_ ).toList
        val ( term, all_vars ) = strip_lambdas( term_, fv )
        //create the type of q
        val qtype = all_vars.foldRight( term.ty )( { case ( v, t ) => v.ty -> t } )
        // apply it to the arguments
        val q_function = Apps( Const( name, qtype ), all_vars )
        // build the formula equating it to the stripped term
        val eq: Formula = Eq( q_function, term )
        // and close the formula universally
        val axiom = all_vars.foldRight( eq ) { case ( v, f ) => All( v, f ) }
        axiom
      }
    }
    qaxioms ++: seq0
  }

}
