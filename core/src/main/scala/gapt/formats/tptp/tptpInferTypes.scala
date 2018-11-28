package gapt.formats.tptp

import gapt.expr._
import gapt.expr.arithmetic.int.TInt
import gapt.formats.babel.{BabelSignature, Notation, Notations, Precedence}
import gapt.proofs.Context

import scala.collection.mutable

object tptpInferTypes {
  case class Context(constants: Map[String, Ty], variables: Map[String, Ty],
                     types: Map[preExpr.Type, Ty], memo : ExpressionMemoization ) {
    def updatedC( cname: String, ty: Ty ) = {
      Context(constants + ((cname, ty)), variables, types, memo)
    }
    def updatedV( cname: String, ty: Ty ) = {
      Context(constants, variables + ((cname, ty)), types, memo)
    }
    def updatedT( cname: preExpr.Type, ty: Ty ) = {
      Context(constants, variables, types+ ((cname, ty)), memo)
    }
  }
  object Context {
    def default_types() = Map[preExpr.Type, Ty](
      preExpr.BaseType( "o", Nil ) -> To,
      preExpr.BaseType( "i", Nil ) -> Ti,
      preExpr.BaseType( "$o", Nil ) -> To,
      preExpr.BaseType( "$i", Nil ) -> Ti,
      preExpr.BaseType( "$int", Nil ) -> TInt )

    def default_constants() = Map[String, Ty](
      "$uminus" -> ( TInt ->: TInt ),
      "$sum" -> ( TInt ->: ( TInt ->: TInt ) ),
      "$product" -> ( TInt ->: ( TInt ->: TInt ) ),
      "$difference" -> ( TInt ->: ( TInt ->: TInt ) ),
      "$less" -> ( TInt ->: ( TInt ->: To ) ),
      "$lesseq" -> ( TInt ->: ( TInt ->: To ) ),
      "$greater" -> ( TInt ->: ( TInt ->: To ) ),
      "$greatereq" -> ( TInt ->: ( TInt ->: To ) ),
    )
    val empty = Context( default_constants, Map(), default_types, ExpressionMemoization() )
  }

  def apply( file: TptpFile ) = if ( file.inputs.isEmpty ) file else {
    val ( inputs_, _ ) = file.inputs.foldLeft( ( Seq[TptpInput](), Context.empty ) )( ( acc, x ) => {
      val ( in, context ) = process( x )( acc._2 )
      ( acc._1 :+ in, context )
    } )
    TptpFile( inputs_ )
  }

  def process( input: TptpInput )( implicit context: Context ): ( TptpInput, Context ) = input match {
    case TypeDeclaration( language, name, ty_name, ty_definition, annotations ) =>
      val context_ = context.updatedC( ty_name, inferType( ty_definition ) )
      ( input, context_ )
    case AnnotatedFormula( language, name, role, formula, annotations ) =>
      ( input, context )
    case AnnotatedPreFormula( language, name, role, formula, annotations ) =>
      val f = infer( formula ).asInstanceOf[Formula]
      //val f = preExpr.toRealExpr( preExpr.TypeAnnotation( formula, preExpr.Bool ), TptpBabelSignature( context.cmap ) )
      ( AnnotatedFormula( language, name, role, f, annotations ), context )
    case IncludeDirective( fileName, formulaSelection ) =>
      ( input, context )
  }

  def infer( e: preExpr.Expr )( implicit context: Context ): Expr = {
    //println( s"inferring type of ${e}" )
    try {
      e match {
        case preExpr.Ident(name, ty, params) if isNumeral(name) =>
          context.memo.Const(name, TBase("$int"))
        case preExpr.Ident(name, ty, params) if context.constants.contains(name) =>
          context.memo.Const(name, context.constants(name))
        case preExpr.Ident(name, ty, params) if context.variables.contains(name) =>
          context.memo.Var(name, context.variables(name))
        case preExpr.Ident(name, ty, params) if isTptpVar(name) =>
          context.memo.Var(name, inferType(ty))
        case preExpr.Ident(name, ty, params) => //if !isTptpVar(name)
          context.memo.Const(name, inferType(ty)) //TODO: find better solution for quoted identifiers - atm they have to be declared
        case preExpr.LocAnnotation(e, _) => infer(e)
        case preExpr.TypeAnnotation(e, t) => infer(e) //TODO: do something with annotations
        case preExpr.App(preExpr.Ident(ForallC.name, _, _), preExpr.Abs(v, e)) =>
          val v1@Var(name, ty) = infer(v)(context)
          val old_ty = context.variables.get(name)
          val e1 = infer(e)(context.updatedV(name, ty))
          if (old_ty.nonEmpty) { context.updatedV(name, old_ty.get) }
          All(v1, e1)
        case preExpr.App(preExpr.Ident(ExistsC.name, _, _), preExpr.Abs(v, e)) =>
          val v1@Var(name, ty) = infer(v)(context)
          val old_ty = context.variables.get(name)
          val e1 = infer(e)(context.updatedV(name, ty))
          if (old_ty.nonEmpty) { context.updatedV(name, old_ty.get) }
          Ex(v1, e1)
        case preExpr.App(preExpr.App(preExpr.Ident(EqC.name, _, _), s), t) =>
          val s1 = infer(s)
          val s2 = infer(t)
          context.memo.Eq(s1, s2)
        case preExpr.App(s, t) =>
          val s1 = infer(s)
          val t1 = infer(t)
          context.memo.App(s1, t1)
        case preExpr.Abs(preExpr.Ident(name, ty, params), e) =>
          val context_ = context.updatedC(name, inferType(ty))
          context.memo.Abs(Var(name, inferType(ty)), infer(e)(context_))

        case preExpr.Quoted(e, ty, fvs) => context.memo.Expr(e)
      }
    } catch {
      case e : IllegalArgumentException =>
        println(s"Exception context:")
        println(s"Consts:\n${context.constants}")
        println(s"Vars:\n${context.variables}")
        println(s"Types:\n${context.types}")
        throw new Exception(e)
    }
  }

  def inferType( t: preExpr.Type )( implicit context: Context ): Ty = t match {
    //context overrides the actual type
    case preExpr.BaseType( name, _ ) if context.types.contains( t ) =>
      context.types( t )
    case preExpr.VarType( name ) if context.types.contains( t ) =>
      context.types( t )
    case preExpr.BaseType( name, args ) =>
      TBase( name, args.map( inferType( _ ) ) )
    case preExpr.ArrType( s, t ) => TArr( inferType( s ), inferType( t ) )

    case _                       => throw new IllegalArgumentException( s"Shouldn't infer types for ${t.toString}" )
    /*
    case preExpr.VarType( name )  => TVar( name )
    case preExpr.MetaType( name ) => TVar( s"mtype#${name.toString}" ) //TODO: what else to do with meta vars?
    case preExpr.ArrType( s, t )  => TArr( inferType( s ), inferType( t ) )
    */
  }

  def isTptpVar( s: String ) = s.nonEmpty && s( 0 ).isUpper
  def isNumeral( s: String ) = s.nonEmpty && ( ( s( 0 ) == '-' ) || ( s( 0 ).isDigit ) ) && s.tail.forall( _.isDigit )

}

case class TptpBabelSignature( constants: Map[String, Const] ) extends BabelSignature {

  def signatureLookup( s: String ): BabelSignature.VarConst = s match {
    case s if constants contains s         => BabelSignature.IsConst( constants( s ) )
    case s if s.nonEmpty && s( 0 ).isUpper => BabelSignature.IsVar
    case _                                 => BabelSignature.IsUnknownConst
  }

  val notations = Context.default.get[Notations] ++
    Seq( "<=", ">=", "<", ">" ).map( c => Notation.Infix( c, Precedence.infixRel ) ) ++
    Seq( "+" ).map( c => Notation.Infix( c, Precedence.plusMinus ) ) ++
    Seq( "*", "/" ).map( c => Notation.Infix( c, Precedence.timesDiv ) )

  def notationsForToken( token: Notation.Token ): Option[Notation] = notations.byToken.get( token )
  def notationsForConst( const: Notation.ConstName ): List[Notation] = notations.byConst( const )

  def defaultTypeToI: Boolean = true
}