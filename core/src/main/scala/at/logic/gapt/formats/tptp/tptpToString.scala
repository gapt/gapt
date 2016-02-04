package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._

object tptpToString {

  def tptpInput( input: TptpInput ): String = input match {
    case AnnotatedFormula( language, name, role, formula, annots ) =>
      s"${atomic_word( language )}(${atomic_word( name )}, $role, ${expression( formula )}${annotations( annots )}).\n"
    case IncludeDirective( fileName, Seq() ) => s"include(${single_quoted( fileName )}).\n"
  }

  def annotations( annots: Seq[LambdaExpression] ): String = annots.map( expression ).map( ", " + _ ).mkString

  def expression( expr: LambdaExpression ): String = expr match {
    case GeneralList( elements @ _* ) =>
      s"[${elements map expression mkString ", "}]"
    case GeneralColon( a, b ) =>
      s"${expression( a )}:${expression( b )}"

    case And( Imp( a, b ), Imp( b_, a_ ) ) if a == a_ && b == b_ =>
      s"(${expression( a )} <=> ${expression( b )})"

    case Top()             => "$true"
    case Bottom()          => "$false"
    case Const( c, _ )     => atomic_word( c )
    case Var( name, _ )    => variable( name )
    case Neg( Eq( a, b ) ) => s"(${expression( a )} != ${expression( b )})"
    case Neg( f )          => s"(~ ${expression( f )})"
    case Eq( a, b )        => s"(${expression( a )} = ${expression( b )})"
    case And( a, b )       => s"(${expression( a )} & ${expression( b )})"
    case Or( a, b )        => s"(${expression( a )} | ${expression( b )})"
    case Imp( a, b )       => s"(${expression( a )} => ${expression( b )})"
    case All.Block( vs, bd ) if vs.nonEmpty =>
      val ( vs_, bd_ ) = renameVars( vs, bd )
      s"(![${vs_ map expression mkString ","}]: ${expression( bd_ )})"
    case Ex.Block( vs, bd ) if vs.nonEmpty =>
      val ( vs_, bd_ ) = renameVars( vs, bd )
      s"(?[${vs_ map expression mkString ","}]: ${expression( bd_ )})"
    case Apps( Const( hd, _ ), args ) if expr.exptype.isInstanceOf[TBase] =>
      s"${atomic_word( hd )}(${args map expression mkString ", "})"
    case App( a, b ) => s"(${expression( a )} @ ${expression( b )})"
  }

  def renameVarName( name: String ) =
    name.toUpperCase match {
      case upper @ upperWordRegex() => upper
      case _ =>
        "X" + name.toUpperCase match {
          case xupper @ upperWordRegex() => xupper
          case _                         => "X"
        }
    }
  def renameVar( v: Var ) = Var( renameVarName( v.name ), v.exptype )
  def renameVars( vars: Seq[Var], body: LambdaExpression ): ( Seq[Var], LambdaExpression ) = {
    val nameGen = rename.awayFrom( freeVariables( body ) -- vars )
    val newVars = for ( fv <- vars ) yield nameGen.fresh( renameVar( fv ) )
    ( newVars, Substitution( vars zip newVars )( body ) )
  }

  private val lowerWordRegex = "[a-z][A-Za-z0-9_]*".r
  private val definedOrSystemWord = "[$][$]?[A-Za-z0-9_]*".r
  private val singleQuoteAllowedRegex = """[\]-~ -&(-\[\\']+""".r
  def atomic_word( name: String ): String = name match {
    case lowerWordRegex()      => name
    case definedOrSystemWord() => name
    case _                     => single_quoted( name )
  }
  def single_quoted( name: String ): String = name match {
    case singleQuoteAllowedRegex() =>
      "'" + name.replace( "\\", "\\\\" ).replace( "'", "\\'" ) + "'"
  }

  private val upperWordRegex = "[A-Z][A-Za-z0-9_]*".r
  def variable( name: String ): String = name match {
    case upperWordRegex() => name
  }

}
