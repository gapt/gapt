package at.logic.gapt.formats.babel

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.utils.Doc
import Doc._

/**
 * Exports lambda expressions in the Babel format.
 * You probably do not want to use this class, use one of [[at.logic.gapt.expr.Expr#toString expression.toString]],
 * [[at.logic.gapt.expr.Expr#toSigRelativeString .toSigRelativeString]], or
 * [[at.logic.gapt.expr.Expr#toAsciiString .toAsciiString]] instead.
 * These are all implemented using this class.
 *
 * @param unicode  Whether to output logical connectives using Unicode symbols.
 * @param sig  The Babel signature, to decide whether we need to escape constants because they
 *             do not fit the naming convention.
 */
class BabelExporter( unicode: Boolean, sig: BabelSignature, omitTypes: Boolean = false ) {

  val defaultIndent = 2
  val lineWidth = 80

  def nest( doc: Doc, j: Int = defaultIndent ): Doc =
    doc.group.nest( j )

  protected def group( doc: Doc ): Doc = doc.group

  protected def parens( doc: Doc ): Doc = "(" <> doc <> ")"

  def knownConstantTypesFromSig( consts: Iterable[Const] ): Iterable[( String, Const )] =
    consts flatMap { c =>
      sig.signatureLookup( c.name ) match {
        case BabelSignature.IsConst( `c` ) => // FIXME: this completely wrong now
          Some( c.name -> c )
        case _ => None
      }
    }

  def export( expr: Expr ): String = {
    val knownTypesFromSig = knownConstantTypesFromSig( constants.all( expr ) )
    group( show( expr, false, Set(), knownTypesFromSig.toMap, prio.max )._1 ).render( lineWidth )
  }
  def export( sequent: HOLSequent ): String = {
    val knownTypesFromSig = knownConstantTypesFromSig( sequent.elements.view.flatMap( constants.all ).toSet )
    group( show( sequent, Set(), knownTypesFromSig.toMap )._1 ).render( lineWidth )
  }
  def export( ty: Ty ): String = show( ty, needParens = false ).group.render( lineWidth )

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

  def show( sequent: HOLSequent, bound: Set[String], t0: Map[String, VarOrConst] ): ( Doc, Map[String, VarOrConst] ) = {
    var t1 = t0
    val docSequent = sequent map { formula =>
      val ( formulaDoc, t1_ ) = show( formula, true, bound, t1, prio.max )
      t1 = t1_
      formulaDoc
    }
    ( sep( docSequent.antecedent.toList, "," <> line ) </>
      ( if ( unicode ) "⊢" else ":-" ) </>
      sep( docSequent.succedent.toList, "," <> line ),
      t1 )
  }

  /**
   * Converts a lambda expression into a document.
   *
   * At every point in the conversion, we keep track of:
   *
   *  1. Whether the parser will already know the type of this expression (by inference)
   *  1. What type the free identifiers have.
   *  1. What priority the enclosing operator has.
   *
   * @param expr  The lambda expression to convert.
   * @param knownType  Whether we already know the type of this expression.
   * @param bound  Names bound by enclosing binders.
   * @param t0  Already used free identifiers, together with the variable or constant they represent.
   * @param p  The priority of the enclosing operator.
   * @return  Pretty-printed document and the free identifiers.
   */
  def show(
    expr:      Expr,
    knownType: Boolean,
    bound:     Set[String],
    t0:        Map[String, VarOrConst],
    p:         Int ): ( Doc, Map[String, VarOrConst] ) =
    expr match {
      case Top() if !bound( TopC.name )       => ( if ( unicode ) "⊤" else "true", t0 )
      case Bottom() if !bound( BottomC.name ) => ( if ( unicode ) "⊥" else "false", t0 )

      case Apps( c @ Const( rel, _, _ ), Seq( a, b ) ) if infixRel( rel ) && expr.ty == To =>
        showBinOp( c, prio.infixRel, 0, 0, a, b, true, bound, t0, p )
      case Apps( c @ Const( "+", _, _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.plusMinus, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "-", _, _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.plusMinus, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "*", _, _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.timesDiv, 1, 0, a, b, knownType, bound, t0, p )
      case Apps( c @ Const( "/", _, _ ), Seq( a, b ) ) =>
        showBinOp( c, prio.timesDiv, 1, 0, a, b, knownType, bound, t0, p )

      case Eq( a, b ) if !bound( EqC.name ) =>
        val ( a_, t1 ) = show( a, false, bound, t0, prio.infixRel )
        val ( b_, t2 ) = show( b, true, bound, t1, prio.infixRel )
        ( parenIf( p, prio.infixRel, a_ <+> "=" </> b_ ), t2 )

      case Neg( e ) if !bound( NegC.name ) =>
        val ( e_, t1 ) = show( e, true, bound, t0, prio.quantOrNeg + 1 )
        ( parenIf( p, prio.quantOrNeg, ( if ( unicode ) "¬" else "-" ) <> e_ ), t1 )

      case And( Imp( a, b ), Imp( b_, a_ ) ) if a == a_ && b == b_ && !bound( AndC.name ) && !bound( ImpC.name ) =>
        showBin( "<->", prio.bicond, 0, 0, a, b, true, bound, t0, p )
      case And( a, b ) if !bound( AndC.name ) =>
        showBin( if ( unicode ) "∧" else "&", prio.conj, 1, 0, a, b, true, bound, t0, p )
      case Or( a, b ) if !bound( OrC.name ) =>
        showBin( if ( unicode ) "∨" else "|", prio.disj, 1, 0, a, b, true, bound, t0, p )
      case Imp( a, b ) if !bound( ImpC.name ) =>
        showBin( if ( unicode ) "⊃" else "->", prio.impl, 0, 1, a, b, true, bound, t0, p )

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

      case expr @ Const( name, ty, params ) =>
        // FIXME(gabriel): type parameter syntax
        if ( bound( name ) || t0.get( name ).exists { _ != expr } || sig.signatureLookup( name ).isVar )
          ( "#c(" <> showName( name ) <> showTyParams( params ) <> ":" </> show( ty, false ) <> ")", t0 )
        else if ( omitTypes || ( ( ty == Ti || knownType ) && params.isEmpty ) || t0.get( name ).contains( expr ) )
          ( showName( name ), t0 + ( name -> expr ) )
        else
          ( parenIf( p, prio.typeAnnot, showName( name ) <> showTyParams( params )
            <> ":" <> show( ty, false ) ), t0 + ( name -> expr ) )
      case expr @ Var( name, ty ) =>
        if ( t0.get( name ).exists { _ != expr } || ( !bound( name ) && !sig.signatureLookup( name ).isVar ) )
          ( "#v(" <> showName( name ) <> ":" </> show( ty, false ) <> ")", t0 )
        else if ( omitTypes || ty == Ti || knownType || t0.get( name ).contains( expr ) )
          ( showName( name ), t0 + ( name -> expr ) )
        else
          ( parenIf( p, prio.typeAnnot, showName( name ) <> ":" <> show( ty, false ) ), t0 + ( name -> expr ) )
    }

  def showTyParams( params: List[Ty] ): Doc =
    if ( params.isEmpty ) "" else
      "{" <> wordwrap( params.map( show( _, params.size > 1 ) ) ) <> "}"

  def showApps(
    expr:      Expr,
    knownType: Boolean,
    bound:     Set[String],
    t0:        Map[String, VarOrConst],
    p:         Int ): ( Doc, Map[String, VarOrConst] ) = {
    val Apps( hd, args ) = expr
    val hdSym = hd match {
      case Const( n, _, _ ) => Some( n )
      case Var( n, _ )      => Some( n )
      case _                => None
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
        if ( args_.size == 1 ) args_.head else wordwrap( args_, "," ) ) ) )

    val hdKnown1 = hdSym.exists { n => t1 get n contains hd }
    if ( omitTypes || knownType || expr.ty == Ti || hdKnown1 ) {
      val ( hd_, t2 ) = show( hd, true, bound, t1, prio.app )
      ( showFunCall( hd_, args_, p ), t2 )
    } else {
      val ( hd_, t2 ) = show( hd, true, bound, t1, prio.typeAnnot )
      ( parenIf( p, prio.typeAnnot, showFunCall( hd_, args_, prio.typeAnnot ) <> ":" </> show( expr.ty, false ) ), t2 )
    }
  }

  def showBin(
    sym:           String,
    prio:          Int,
    leftPrioBias:  Int,
    rightPrioBias: Int,
    a:             Expr,
    b:             Expr,
    knownType:     Boolean,
    bound:         Set[String],
    t0:            Map[String, VarOrConst],
    p:             Int ): ( Doc, Map[String, VarOrConst] ) = {
    val ( a_, t1 ) = show( a, knownType, bound, t0, prio + leftPrioBias )
    val ( b_, t2 ) = show( b, knownType, bound, t1, prio + rightPrioBias )
    ( parenIf( p, prio, a_ <+> sym </> b_ ), t2 )
  }

  def showBinOp(
    c:             Const,
    prio:          Int,
    leftPrioBias:  Int,
    rightPrioBias: Int,
    a:             Expr,
    b:             Expr,
    knownType:     Boolean,
    bound:         Set[String],
    t0:            Map[String, VarOrConst],
    p:             Int ): ( Doc, Map[String, VarOrConst] ) = {
    val Const( cn, argt1 ->: argt2 ->: rett, _ ) = c
    val cKnown = t0.get( cn ).contains( c )
    if ( t0.get( cn ).exists { _ != c } ) {
      showApps( c( a, b ), knownType, bound, t0, p )
    } else if ( knownType || rett == Ti || cKnown ) {
      showBin( cn, prio, leftPrioBias, rightPrioBias, a, b, cKnown, bound, t0 + ( cn -> c ), p )
    } else {
      val ( expr_, t1 ) = showBinOp( c, prio, leftPrioBias, rightPrioBias, a, b,
        true, bound, t0, BabelExporter.this.prio.typeAnnot )
      ( parenIf( p, BabelExporter.this.prio.typeAnnot,
        expr_ <> ":" </> show( rett, false ) ), t1 )
    }
  }

  def showQuant(
    sym:   String,
    v:     Var,
    e:     Expr,
    bound: Set[String],
    t0:    Map[String, VarOrConst],
    p:     Int ): ( Doc, Map[String, VarOrConst] ) = {
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

  val safeChars = """[A-Za-z0-9 ~!@#$%^&*()_=+{}|;:,./<>?-]|\[|\]""".r
  val asciiUnquotName = """[A-Za-z0-9_]+""".r
  def showName( name: String ): Doc = name match {
    case _ if BabelLexical.keywords( name ) =>
      s"'$name'"
    case _ if unicode && name.nonEmpty && name.forall { BabelLexical.isUnquotNameChar } => name
    case asciiUnquotName() if !unicode => name
    case _ => "'" + name.map {
      case c @ safeChars() =>
        c
      case '\''         => "\\'"
      case '\\'         => "\\\\"
      case c if unicode => c
      case c            => "\\u%04x".format( c.toChar.toInt )
    }.mkString + "'"
  }

  def show( ty: Ty, needParens: Boolean ): Doc = ty match {
    case TBase( name, params ) => wordwrap( showName( name ) :: params.map( show( _, needParens = true ) ) )
    case TVar( name )          => "?" <> showName( name )
    case a ->: b if !needParens =>
      group( show( a, true ) <> ">" <> zeroWidthLine <> show( b, false ) )
    case _ => parens( nest( show( ty, false ) ) )
  }

  def parenIf( enclosingPrio: Int, currentPrio: Int, doc: Doc ): Doc =
    if ( enclosingPrio <= currentPrio ) {
      parens( group( nest( doc ) ) )
    } else if ( enclosingPrio / 2 > currentPrio / 2 ) {
      group( nest( doc ) )
    } else {
      doc
    }
}
