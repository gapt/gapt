package at.logic.gapt.formats.veriT

import at.logic.gapt.language.fol._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.language.lambda.symbols._
import at.logic.gapt.utils.latex._
import java.io._
import org.apache.commons.lang3.StringEscapeUtils
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.language.lambda.types.{ Ti, To }

object VeriTExporter {

  /**
   *  Takes a sequent and generates the input for VeriT as a string.
   *
   * @param s Sequent to export.
   * @return VeriT input.
   */
  def apply( s: FSequent ): String = {
    // Define the logic
    val logic = "(set-logic QF_UF)\n"
    // Declare the function and predicate symbols with arity
    val symbols = getSymbolsDeclaration( ( s._1 ++ s._2 ).asInstanceOf[List[FOLFormula]] )
    // Generate assertions for the antecedent and succedent formulas
    val asserts = getAssertions( s._1.asInstanceOf[List[FOLFormula]], s._2.asInstanceOf[List[FOLFormula]] )
    // Generate the check_sat formula
    val check_sat = "(check-sat)"

    logic + symbols + asserts + check_sat
  }

  /**
   * Takes a sequent and generates the input for VeriT as a file
   *
   * @param s Sequent to export.
   * @param fileName  Output file name.
   * @return File pointing to fileName.
   */
  def apply( s: FSequent, fileName: String ): File = {
    val file = new File( fileName )
    val fw = new FileWriter( file.getAbsoluteFile )
    val bw = new BufferedWriter( fw )
    bw.write( VeriTExporter( s ) )
    bw.close()

    file
  }

  private def getAssertions( ant: List[FOLFormula], succ: List[FOLFormula] ) = {
    val s1 = ant.foldLeft( "" ) {
      case ( acc, f ) =>
        "(assert " + toSMTFormat( f ) + ")\n" + acc
    }

    if ( succ.length == 0 ) {
      s1
    } else {
      val negs = succ.map( x => FOLNeg( x ) )
      val disj = FOLOr( negs )
      s1 + "(assert " + toSMTFormat( disj ) + ")\n"
    }
  }

  // Gets all the symbols and arities that occur in the formulas of the list
  private def getSymbolsDeclaration( flst: List[FOLFormula] ) = {
    val symbols = flst.foldLeft( Set[( String, Int, TA )]() )( ( acc, f ) =>
      getSymbols( f ) ++ acc )
    symbols.foldLeft( "(declare-sort S 0)\n" ) {
      case ( acc, t ) => t._3 match {
        // It is an atom
        case To => acc ++ "(declare-fun " + t._1 + " (" + "S " * t._2 + ") Bool)\n"
        // It is a function
        case Ti => acc ++ "(declare-fun " + t._1 + " (" + "S " * t._2 + ") S)\n"
        case _  => throw new Exception( "Unexpected type for function or predicate: " + t._3 )
      }
    }
  }

  // TODO: Implement in hol/fol??
  // (Note: here we would only use propositional formulas, but it is already
  // implemented for quantifiers just in case...)
  private def getSymbols( f: FOLExpression ): Set[( String, Int, TA )] = f match {
    case FOLVar( s )   => Set( ( toSMTString( s, true ), 0, Ti ) )
    case FOLConst( s ) => Set( ( toSMTString( s, false ), 0, Ti ) )
    case FOLAtom( pred, args ) =>
      Set( ( toSMTString( pred, false ), args.size, f.exptype ) ) ++ args.foldLeft( Set[( String, Int, TA )]() )( ( acc, f ) => getSymbols( f ) ++ acc )
    case FOLFunction( fun, args ) =>
      Set( ( toSMTString( fun, false ), args.size, f.exptype ) ) ++ args.foldLeft( Set[( String, Int, TA )]() )( ( acc, f ) => getSymbols( f ) ++ acc )
    case FOLAnd( f1, f2 )   => getSymbols( f1 ) ++ getSymbols( f2 )
    case FOLOr( f1, f2 )    => getSymbols( f1 ) ++ getSymbols( f2 )
    case FOLImp( f1, f2 )   => getSymbols( f1 ) ++ getSymbols( f2 )
    case FOLNeg( f1 )       => getSymbols( f1 )
    case FOLAllVar( _, f1 ) => getSymbols( f1 )
    case FOLExVar( _, f1 )  => getSymbols( f1 )
    case _                  => throw new Exception( "Undefined formula: " + f )
  }

  private def toSMTFormat( f: FOLExpression ): String = f match {
    case FOLTopC       => "true"
    case FOLBottomC    => "false"
    case FOLVar( s )   => toSMTString( s, true )
    case FOLConst( s ) => toSMTString( s, false )
    case FOLAtom( pred, args ) =>
      if ( args.size == 0 ) {
        toSMTString( pred, false )
      } else {
        "(" + toSMTString( pred, false ) + " " + args.foldLeft( "" )( ( acc, t ) => toSMTFormat( t ) + " " + acc ) + ")"
      }
    // Functions should have arguments.
    case FOLFunction( fun, args ) => "(" + toSMTString( fun, false ) + " " + args.foldRight( "" )( ( t, acc ) => toSMTFormat( t ) + " " + acc ) + ")"
    case FOLAnd( f1, f2 )         => "(and " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case FOLOr( f1, f2 )          => "(or " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case FOLImp( f1, f2 )         => "(=> " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case FOLNeg( f1 )             => "(not " + toSMTFormat( f1 ) + ")"
    case _                        => throw new Exception( "Undefined formula for SMT: " + f )
  }

  // Note: not an exhaustive list
  private val smt_keywords = List(
    "set-logic",
    "QF_UF",
    "declare-sort",
    "declare-fun",
    "assert",
    "not", "and", "or", "xor",
    "as", "push",
    "true", "false" )

  // Transforms the string into ASCII and checks if 
  // it does not clash with veriT keywords.
  private def toSMTString( s: SymbolA, isVar: Boolean ): String = toSMTString( s.toString, isVar )
  private def toSMTString( s: String, isVar: Boolean ): String = {
    // It's a number, append a character before it.
    val ascii = if ( s.forall( c => Character.isDigit( c ) ) ) {
      "n" + s
    } else {
      // Attempt #3
      StringEscapeUtils.escapeJava( s ).replaceAll( """\\""", "" )
    }

    val clash = if ( smt_keywords.contains( ascii ) ) ascii + "_clash"
    else ascii

    // FIXME: this is a hack to get VeriTParser to recognize variables
    if ( isVar ) clash + "$"
    else clash
  }
}
