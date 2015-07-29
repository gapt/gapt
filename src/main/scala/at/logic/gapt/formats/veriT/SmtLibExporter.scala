package at.logic.gapt.formats.veriT

import at.logic.gapt.expr._
import at.logic.gapt.expr._
import at.logic.gapt.expr._
import java.io._
import org.apache.commons.lang3.StringEscapeUtils
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.expr.{ Ti, To }

object SmtLibExporter {

  /**
   *  Takes a sequent and generates the SMT-LIB benchmark as a string.
   *
   * @param s Sequent to export.
   * @return SMT-LIB benchmark.
   */
  def apply( s: HOLSequent ): String = {
    // Define the logic
    val logic = "(set-logic QF_UF)\n"
    // Declare the function and predicate symbols with arity
    val symbols = getSymbolsDeclaration( ( s.antecedent ++ s.succedent ).map( _.asInstanceOf[FOLFormula] ) )
    // Generate assertions for the antecedent and succedent formulas
    val asserts = getAssertions( s.antecedent.map( _.asInstanceOf[FOLFormula] ), s.succedent.map( _.asInstanceOf[FOLFormula] ) )
    // Generate the check_sat formula
    val check_sat = "(check-sat)"

    logic + symbols + asserts + check_sat
  }

  /**
   * Takes a sequent and generates the SMT-LIB benchmark as a file
   *
   * @param s Sequent to export.
   * @param fileName  Output file name.
   * @return File pointing to fileName.
   */
  def apply( s: HOLSequent, fileName: String ): File = {
    val file = new File( fileName )
    val fw = new FileWriter( file.getAbsoluteFile )
    val bw = new BufferedWriter( fw )
    bw.write( SmtLibExporter( s ) )
    bw.close()

    file
  }

  private def getAssertions( ant: Seq[FOLFormula], succ: Seq[FOLFormula] ) =
    ( ant ++ succ.map( Neg( _ ) ) ).map { formula =>
      s"(assert ${toSMTFormat( formula )})\n"
    }.mkString

  // Gets all the symbols and arities that occur in the formulas of the list
  private def getSymbolsDeclaration( flst: Seq[FOLFormula] ) = {
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
    case Eq( lhs, rhs ) => Set( lhs, rhs ) flatMap getSymbols
    case FOLVar( s )    => Set( ( toSMTString( s, true ), 0, Ti ) )
    case FOLConst( s )  => Set( ( toSMTString( s, false ), 0, Ti ) )
    case FOLAtom( pred, args ) =>
      Set( ( toSMTString( pred, false ), args.size, f.exptype ) ) ++ args.foldLeft( Set[( String, Int, TA )]() )( ( acc, f ) => getSymbols( f ) ++ acc )
    case FOLFunction( fun, args ) =>
      Set( ( toSMTString( fun, false ), args.size, f.exptype ) ) ++ args.foldLeft( Set[( String, Int, TA )]() )( ( acc, f ) => getSymbols( f ) ++ acc )
    case And( f1, f2 )    => getSymbols( f1 ) ++ getSymbols( f2 )
    case Or( f1, f2 )     => getSymbols( f1 ) ++ getSymbols( f2 )
    case Imp( f1, f2 )    => getSymbols( f1 ) ++ getSymbols( f2 )
    case Neg( f1 )        => getSymbols( f1 )
    case All( _, f1 )     => getSymbols( f1 )
    case Ex( _, f1 )      => getSymbols( f1 )
    case Top() | Bottom() => Set()
    case _                => throw new Exception( "Undefined formula: " + f )
  }

  private def toSMTFormat( f: FOLExpression ): String = f match {
    case Top()                    => "true"
    case Bottom()                 => "false"
    case FOLVar( s )              => toSMTString( s, true )
    case FOLAtom( pred, args )    => toSMTFormat( pred, args )
    case FOLFunction( fun, args ) => toSMTFormat( fun, args )
    case And( f1, f2 )            => "(and " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case Or( f1, f2 )             => "(or " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case Imp( f1, f2 )            => "(=> " + toSMTFormat( f1 ) + " " + toSMTFormat( f2 ) + ")"
    case Neg( f1 )                => "(not " + toSMTFormat( f1 ) + ")"
    case _                        => throw new Exception( "Undefined formula for SMT: " + f )
  }

  private def toSMTFormat( head: String, args: Seq[FOLTerm] ): String =
    if ( args.isEmpty )
      head
    else
      s"(${toSMTString( head, false )} ${args.map( toSMTFormat ).mkString( " " )})"

  // Note: not an exhaustive list
  private val smt_keywords = List(
    "set-logic",
    "QF_UF",
    "declare-sort",
    "declare-fun",
    "assert",
    "not", "and", "or", "xor",
    "as", "push",
    "true", "false"
  )

  // Transforms the string into ASCII and checks if 
  // it does not clash with SMT-LIB keywords.
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
