package gapt.formats.tptp

import gapt.expr._
import gapt.expr.preExpr.FlatOpsChild

object tptpToString {

  def tptpInput( input: TptpInput ): String = input match {
    case AnnotatedFormula( language, name, role, formula, annots ) =>
      s"${atomic_word( language )}(${atomic_word( name )}, $role, ${expression( formula )}${annotations( annots )}).\n"
    //TODO: fix pre formula printing
    case AnnotatedPreFormula( language, name, role, formula, annots ) =>
      s"${atomic_word( language )}(${atomic_word( name )}, $role, ${pre_expression( formula )}, ${annotations( annots )}).\n"
    case IncludeDirective( fileName, None ) => s"include(${single_quoted( fileName )}).\n"
    case IncludeDirective( fileName, Some( seq ) ) =>
      //TODO: check what seq actually contains
      val args = seq.map( single_quoted ).mkString( "[", ", ", "]" )
      s"include(${single_quoted( fileName )}, ${args}).\n"

    case TypeDeclaration( language, name, ty_name, ty_definition, annots ) =>
      s"${atomic_word( language )}(${atomic_word( name )}, type, ${ty_name} : ${complex_type( ty_definition )}, ${annotations( annots )}).\n"
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

    case Iff( a, b ) =>
      binExpr( a, b, p, prio.binary_formula, "<=>" )

    case Top()                              => "$true"
    case Bottom()                           => "$false"
    case Const( c, _, _ )                   => atomic_word( c )
    case Var( name, _ )                     => variable( name )
    case Neg( Eq( a, b ) )                  => binExpr( a, b, p, prio.infix_formula, "!=" )
    case Neg( f )                           => parenIf( p, prio.unitary_formula, s"~ ${expression( f, prio.unitary_formula + 1 )}" )
    case Eq( a, b )                         => binExpr( a, b, p, prio.infix_formula, "=" )
    case And( _, _ )                        => binAssocExpr( expr, p, "&", And )
    case Or( a, b )                         => binAssocExpr( expr, p, "|", Or )
    case Imp( a, b )                        => binExpr( a, b, p, prio.binary_formula, "=>" )
    case All.Block( vs, bd ) if vs.nonEmpty => quant( vs, bd, p, "!" )
    case Ex.Block( vs, bd ) if vs.nonEmpty  => quant( vs, bd, p, "?" )
    case Apps( Const( hd, _, _ ), args ) if expr.ty.isInstanceOf[TBase] =>
      s"${atomic_word( hd )}(${args map expression mkString ", "})"
    case App( a, b ) => binExpr( a, b, p, prio.term, s"@" )
  }

  //TODO: do typed expression printing
  private def pre_expression( expr: preExpr.Expr ): String = expr match {
    case preExpr.Ident( name, ty, None )           => s"Ident(${name}, ${pre_type( ty )})"
    case preExpr.Ident( name, ty, Some( params ) ) => s"Ident(${name}, ${pre_type( ty )}, ${params.map( pre_type ).mkString( ", " )})"
    case preExpr.App( s, t )                       => s"App(${pre_expression( s )}, ${pre_expression( t )})"
    case preExpr.Abs( s, t )                       => s"Abs(${pre_expression( s )}, ${pre_expression( t )})"
    case preExpr.Quoted( e, _, _ )                 => s"Quoted(${expression( e )}, _, _)"
    case preExpr.TypeAnnotation( expr, ty )        => pre_expression( expr )
    case preExpr.LocAnnotation( expr, loc )        => pre_expression( expr )
    case preExpr.FlatOps( children )               => s"FlatOps(${children.map( flatops_child ).mkString( ", " )})"
  }

  private def flatops_child( fo: FlatOpsChild ): String = fo match {
    case Left( ( str, loc ) ) => s"String($str)"
    case Right( expr )        => s"Expr(${pre_expression( expr )})"
  }

  private def pre_type( t: preExpr.Type ): String = t match {
    case preExpr.BaseType( name, params ) => s"BaseType(${name}, ${params.map( pre_type ).mkString( ", " )},)"
    case preExpr.VarType( name )          => s"VarType(${name}})"
    case preExpr.MetaType( name )         => s"VarType(${name.toString}})"
    case preExpr.ArrType( a, b )          => s"ArrType(${pre_type( a )}, ${pre_type( b )})"
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
  def renameVars( f: Formula ): Formula =
    renameVars( freeVariables( f ).toSeq, f )._2.asInstanceOf[Formula]

  private val lowerWordRegex = "[a-z][A-Za-z0-9_]*".r
  private val definedOrSystemWord = "[$][$]?[A-Za-z0-9_]*".r
  private val singleQuoteAllowedRegex = """[\]-~ -&(-\[\\']+""".r
  def atomic_word( name: String ): String = name match {
    case lowerWordRegex()      => name
    case definedOrSystemWord() => name
    case _                     => single_quoted( name )
  }
  def complex_type( ty: preExpr.Type ): String = ty match {
    case preExpr.VarType( name )                             => s"${name}"
    case preExpr.MetaType( name )                            => s"${name}"
    case preExpr.BaseType( name, Nil )                       => s"${name}"
    case preExpr.BaseType( name, args )                      => s"${name}${args.map( complex_type ).mkString( "(", ", ", ")" )}"
    case preExpr.ArrType( t1 @ preExpr.ArrType( _, _ ), t2 ) => s"(${complex_type( t1 )}) > ${complex_type( t2 )}"
    case preExpr.ArrType( t1, t2 )                           => s"${complex_type( t1 )} > ${complex_type( t2 )}"
  }
  def single_quoted( name: String ): String =
    "'" + name.replace( "\\", "\\\\" ).replace( "'", "\\'" ) + "'"

  private val upperWordRegex = "[A-Z][A-Za-z0-9_]*".r
  def variable( name: String ): String = name

}
