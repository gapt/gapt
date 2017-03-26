package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._

object tptpToString {

  def tptpInput( input: TptpInput ): String = input match {
    case AnnotatedFormula( language, name, role, formula, annots ) =>
      s"${atomic_word( language )}(${atomic_word( name )}, $role, ${expression( formula )}${annotations( annots )}).\n"
    case IncludeDirective( fileName, Seq() ) => s"include(${single_quoted( fileName )}).\n"
  }

  def annotations( annots: Seq[Expr] ): String = annots.map( expression ).map( ", " + _ ).mkString

  def expression( expr: Expr ): String = expression( expr, prio.max )

  private object prio {
    val term = 0
    val infix_formula = 2
    val unitary_formula = 4
    val binary_formula = 6
    val max = binary_formula + 2
  }
  private def parenIf( enclosingPrio: Int, currentPrio: Int, inside: String ) =
    if ( enclosingPrio <= currentPrio ) s"($inside)" else inside
  private def binExpr( a: Expr, b: Expr, p: Int, newPrio: Int, op: String ) =
    parenIf( p, newPrio, s"${expression( a, newPrio )} $op ${expression( b, newPrio )}" )
  private def binAssocExpr( expr: Expr, p: Int, op: String, conn: MonoidalBinaryPropConnectiveHelper ) = {
    def leftAssocJuncts( e: Expr ): Seq[Expr] = e match {
      case conn( a, b ) => leftAssocJuncts( a ) :+ b
      case _            => Seq( e )
    }
    parenIf( p, prio.binary_formula, leftAssocJuncts( expr ).map( expression( _, prio.binary_formula ) ).mkString( s" $op " ) )
  }
  private def quant( vs: Seq[Var], bd: Expr, p: Int, q: String ) = {
    val ( vs_, bd_ ) = renameVars( vs, bd )
    parenIf( p, prio.unitary_formula, s"$q[${vs_ map expression mkString ","}]: ${expression( bd_, prio.unitary_formula + 1 )}" )
  }
  private def expression( expr: Expr, p: Int ): String = expr match {
    case GeneralList( elements @ _* ) =>
      s"[${elements map expression mkString ", "}]"
    case GeneralColon( a, b ) =>
      s"${expression( a, prio.term )}:${expression( b, prio.term )}"

    case And( Imp( a, b ), Imp( b_, a_ ) ) if a == a_ && b == b_ =>
      binExpr( a, b, p, prio.binary_formula, "<=>" )

    case Top()                              => "$true"
    case Bottom()                           => "$false"
    case Const( c, _ )                      => atomic_word( c )
    case Var( name, _ )                     => variable( name )
    case Neg( Eq( a, b ) )                  => binExpr( a, b, p, prio.infix_formula, "!=" )
    case Neg( f )                           => parenIf( p, prio.unitary_formula, s"~ ${expression( f, prio.unitary_formula + 1 )}" )
    case Eq( a, b )                         => binExpr( a, b, p, prio.infix_formula, "=" )
    case And( _, _ )                        => binAssocExpr( expr, p, "&", And )
    case Or( a, b )                         => binAssocExpr( expr, p, "|", Or )
    case Imp( a, b )                        => binExpr( a, b, p, prio.binary_formula, "=>" )
    case All.Block( vs, bd ) if vs.nonEmpty => quant( vs, bd, p, "!" )
    case Ex.Block( vs, bd ) if vs.nonEmpty  => quant( vs, bd, p, "?" )
    case Apps( Const( hd, _ ), args ) if expr.ty.isInstanceOf[TBase] =>
      s"${atomic_word( hd )}(${args map expression mkString ", "})"
    case App( a, b ) => binExpr( a, b, p, prio.term, s"@" )
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
  def renameVar( v: Var ) = Var( renameVarName( v.name ), v.ty )
  def renameVars( vars: Seq[Var], body: Expr ): ( Seq[Var], Expr ) = {
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
