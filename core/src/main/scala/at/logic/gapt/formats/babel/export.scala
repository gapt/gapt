package at.logic.gapt.formats.babel

import at.logic.gapt.expr._
import org.kiama.output.PrettyPrinter

class BabelExporter( unicode: Boolean, sig: Signature ) extends PrettyPrinter {

  override val defaultIndent = 2

  override def nest( doc: Doc, j: Indent = defaultIndent ): Doc =
    nesting { i =>
      if ( i > 10 ) doc
      else super.nest( doc, j )
    }

  def export( expr: LambdaExpression ): String = {
    val knownTypesFromSig = constants( expr ) flatMap { c =>
      sig( c.name ) match {
        case IsConst( ast.TypeVar( _ ) ) => None
        case IsConst( astType ) if astType == ast.liftType( c.exptype ) => Some( c.name -> c )
        case _ => None
      }
    }
    pretty( group( show( expr, false, Set(), knownTypesFromSig.toMap, prio.max )._1 ) )
  }

  object prio {
    val ident = 0
    val app = 2
    val timesDiv = 4
    val plusMinus = 6
    val infixRel = 8
    val quantOrNeg = 10
    val conj = 12
    val disj = 16
    val bicond = 18
    val impl = 20
    val typeAnnot = 22
    val lam = 24

    val max = lam + 2
  }

  val infixRel = Set( "<", "<=", ">", ">=" )
  val logicalConstName = Set(
    TopC.name, BottomC.name, NegC.name, AndC.name, OrC.name, ImpC.name,
    ForallC.name, ExistsC.name
  )

  def show(
    expr:      LambdaExpression,
    knownType: Boolean,
    bound:     Set[String],
    t0:        Map[String, LambdaExpression],
    p:         Int
  ): ( Doc, Map[String, LambdaExpression] ) =
    expr match {
      case Top() if !bound( TopC.name )       => ( value( if ( unicode ) "⊤" else "true" ), t0 )
      case Bottom() if !bound( BottomC.name ) => ( value( if ( unicode ) "⊥" else "false" ), t0 )

      case Apps( c @ Const( rel, _ ), Seq( a, b ) ) if infixRel( rel ) && expr.exptype == To =>
        showBinOp( c, prio.infixRel, 0, 0, a, b, true, bound, t0, p )
      case Apps( c @ Const( "+", _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.plusMinus, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "-", _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.plusMinus, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "*", _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.timesDiv, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "/", _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.timesDiv, 1, 0, a, b, knownType, bound, t0, p )

      case Eq( a, b ) if !bound( EqC.name ) =>
        val ( a_, t1 ) = show( a, false, bound, t0, prio.infixRel )
        val ( b_, t2 ) = show( b, true, bound, t1, prio.infixRel )
        ( parenIf( p, prio.infixRel, a_ <+> "=" <@> b_ ), t2 )

      case Neg( e ) if !bound( NegC.name ) =>
        val ( e_, t1 ) = show( e, true, bound, t0, prio.quantOrNeg + 1 )
        ( parenIf( p, prio.quantOrNeg, ( if ( unicode ) "¬" else "-" ) <> e_ ), t1 )

      case And( a, b ) if !bound( AndC.name ) => showBin( if ( unicode ) "∧" else "&", prio.conj, 1, 0, a, b, true, bound, t0, p )
      case Or( a, b ) if !bound( OrC.name )   => showBin( if ( unicode ) "∨" else "|", prio.disj, 1, 0, a, b, true, bound, t0, p )
      case Imp( a, b ) if !bound( ImpC.name ) => showBin( if ( unicode ) "⊃" else "->", prio.impl, 0, 1, a, b, true, bound, t0, p )

      case Abs( v @ Var( vn, vt ), e ) =>
        val ( e_, t1 ) = show( e, knownType, bound + vn, t0 - vn, prio.lam + 1 )
        val v_ =
          if ( vt == Ti || t1.get( vn ).contains( v ) )
            showName( vn )
          else
            parens( showName( vn ) <> ":" <> show( vt, false ) )
        ( parenIf( p, prio.lam, ( if ( unicode ) "λ" else "^" ) <> v_ </> e_ ),
          t1 - vn ++ t0.get( vn ).map { vn -> _ } )

      case All( v, e ) if !bound( ForallC.name ) => showQuant( if ( unicode ) "∀" else "!", v, e, bound, t0, p )
      case Ex( v, e ) if !bound( ExistsC.name )  => showQuant( if ( unicode ) "∃" else "?", v, e, bound, t0, p )

      case Apps( _, args ) if args.nonEmpty      => showApps( expr, knownType, bound, t0, p )

      case Const( name, ty ) =>
        if ( t0.get( name ).exists { _ != expr } || sig.isVar( name ) || logicalConstName( name ) || name == EqC.name )
          ( "#c(" <> showName( name ) <> ":" </> show( ty, false ) <> ")", t0 )
        else if ( ty == Ti || knownType || t0.get( name ).contains( expr ) )
          ( showName( name ), t0 + ( name -> expr ) )
        else
          ( parenIf( p, prio.typeAnnot, showName( name ) <> ":" <> show( ty, false ) ), t0 + ( name -> expr ) )
      case Var( name, ty ) =>
        if ( t0.get( name ).exists { _ != expr } || ( !bound( name ) && !sig.isVar( name ) ) )
          ( "#v(" <> showName( name ) <> ":" </> show( ty, false ) <> ")", t0 )
        else if ( ty == Ti || knownType || t0.get( name ).contains( expr ) )
          ( showName( name ), t0 + ( name -> expr ) )
        else
          ( parenIf( p, prio.typeAnnot, showName( name ) <> ":" <> show( ty, false ) ), t0 + ( name -> expr ) )
    }

  def showApps(
    expr:      LambdaExpression,
    knownType: Boolean,
    bound:     Set[String],
    t0:        Map[String, LambdaExpression],
    p:         Int
  ): ( Doc, Map[String, LambdaExpression] ) = {
    val Apps( hd, args ) = expr
    val hdSym = hd match {
      case Const( n, _ ) => Some( n )
      case Var( n, _ )   => Some( n )
      case _             => None
    }

    val hdKnown0 = hdSym.exists { n => t0 get n contains hd }
    var t1 = t0
    val args_ = for ( arg <- args ) yield {
      val ( arg_, t10 ) = show( arg, hdKnown0, bound, t1, prio.max )
      t1 = t10
      arg_
    }

    def showFunCall( hd_ :Doc, args_ : List[Doc], p: Int ) =
      parenIf( p, prio.app, hd_ ) <> nest( group( parens(
        if ( args_.size == 1 ) args_.head else lsep( args_, comma )
      ) ) )

    val hdKnown1 = hdSym.exists { n => t1 get n contains hd }
    if ( knownType || expr.exptype == Ti || hdKnown1 ) {
      val ( hd_, t2 ) = show( hd, true, bound, t1, prio.app )
      ( showFunCall( hd_, args_, p ), t2 )
    } else {
      val ( hd_, t2 ) = show( hd, true, bound, t1, prio.typeAnnot )
      ( parenIf( p, prio.typeAnnot, showFunCall( hd_, args_, prio.typeAnnot ) <> ":" <@> show( expr.exptype, false ) ), t2 )
    }
  }

  def showBin(
    sym:           String,
    prio:          Int,
    leftPrioBias:  Int,
    rightPrioBias: Int,
    a:             LambdaExpression,
    b:             LambdaExpression,
    knownType:     Boolean,
    bound:         Set[String],
    t0:            Map[String, LambdaExpression],
    p:             Int
  ): ( Doc, Map[String, LambdaExpression] ) = {
    val ( a_, t1 ) = show( a, knownType, bound, t0, prio + leftPrioBias )
    val ( b_, t2 ) = show( b, knownType, bound, t1, prio + rightPrioBias )
    ( parenIf( p, prio, a_ <+> sym <@> b_ ), t2 )
  }

  def showBinOp(
    c:             Const,
    prio:          Int,
    leftPrioBias:  Int,
    rightPrioBias: Int,
    a:             LambdaExpression,
    b:             LambdaExpression,
    knownType:     Boolean,
    bound:         Set[String],
    t0:            Map[String, LambdaExpression],
    p:             Int
  ): ( Doc, Map[String, LambdaExpression] ) = {
    val Const( cn, argt1 -> ( argt2 -> rett ) ) = c
    val cKnown = t0.get( cn ).contains( c )
    if ( t0.get( cn ).exists { _ != c } ) {
      showApps( c( a, b ), knownType, bound, t0, p )
    } else if ( knownType || rett == Ti || cKnown ) {
      showBin( cn, prio, leftPrioBias, rightPrioBias, a, b, cKnown, bound, t0 + ( cn -> c ), p )
    } else {
      val ( expr_, t1 ) = showBinOp( c, prio, leftPrioBias, rightPrioBias, a, b,
        true, bound, t0, BabelExporter.this.prio.typeAnnot )
      ( parenIf( p, BabelExporter.this.prio.typeAnnot,
        expr_ <> ":" <@> show( rett, false ) ), t1 )
    }
  }

  def showQuant(
    sym:   String,
    v:     Var,
    e:     LambdaExpression,
    bound: Set[String],
    t0:    Map[String, LambdaExpression],
    p:     Int
  ): ( Doc, Map[String, LambdaExpression] ) = {
    val Var( vn, vt ) = v
    val ( e_, t1 ) = show( e, true, bound + vn, t0 - vn, prio.quantOrNeg + 1 )
    val v_ =
      if ( vt == Ti || t1.get( vn ).contains( v ) )
        showName( vn )
      else
        parens( showName( vn ) <> ":" <> show( vt, false ) )
    ( parenIf( p, prio.quantOrNeg, sym <> v_ </> e_ ),
      t1 - vn ++ t0.get( vn ).map { vn -> _ } )
  }

  val unquotedName = """[A-Za-z0-9_$]+""".r
  val safeChars = """[A-Za-z0-9 ~!@#$%^&*()_=+{}|;:,./<>?-]|\[|\]""".r
  def showName( name: String ): Doc = name match {
    case _ if BabelLexical.keywords( name ) =>
      s"'$name'"
    case unquotedName() => name
    case _ => "'" + name.map {
      case c @ safeChars() =>
        c
      case '''          => "\\'"
      case '\\'         => "\\\\"
      case c if unicode => c
      case c            => "\\u%04x".format( c.toChar.toInt )
    }.mkString + "'"
  }

  def show( ty: Ty, needParens: Boolean ): Doc = ty match {
    case TBase( name ) => showName( name )
    case a -> b if !needParens =>
      group( show( a, true ) <> ">" <@@> show( b, false ) )
    case _ => parens( nest( show( ty, false ) ) )
  }

  def parenIf( enclosingPrio: Int, currentPrio: Int, doc: Doc ) =
    if ( enclosingPrio <= currentPrio ) {
      parens( group( nest( doc ) ) )
    } else if ( enclosingPrio / 2 > currentPrio / 2 ) {
      group( nest( doc ) )
    } else {
      doc
    }
}
