package gapt.formats.latex

import gapt.expr._
import gapt.proofs.{ HOLSequent, SequentProof }
import gapt.utils.Doc
import Doc._
import gapt.expr.VarOrConst
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.ty.{ TArr, TBase, TVar, Ty }

object LatexExporter {

  // Expressions

  def apply( e: Expr ): String = doc( e ).render( 80 )
  def apply( sequent: HOLSequent ): String = doc( sequent ).render( 80 )

  def doc( sequent: HOLSequent ): Doc =
    ( Doc.wordwrap2( sequent.antecedent.map( doc ), "," ) <+> "\\vdash" </>
      Doc.wordwrap2( sequent.succedent.map( doc ), "," ) ).group

  def doc( e: Expr ): Doc = expr( e, prio.max )

  private object prio {
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
  private def parenIf( enclosingPrio: Int, currentPrio: Int, inside: Doc ): Doc =
    if ( enclosingPrio <= currentPrio ) "(" <> inside <> ")" else inside
  private def binExpr( a: Expr, b: Expr, p: Int, newPrio: Int, op: Doc ): Doc =
    parenIf( p, newPrio, expr( a, newPrio ) <+> op </> expr( b, newPrio ) ).group.nest( 2 )
  private def quant( f: Expr, v: Var, p: Int, op: Doc ): Doc =
    parenIf( p, prio.quantOrNeg, op <+> escapeName( v.name ) <> "\\:" </> expr( f, prio.quantOrNeg + 1 ) ).group
  private val relOps = Map( "=" -> "=", "<" -> "<", ">" -> ">", "<=" -> "\\leq", ">=" -> "\\geq" )
  private def expr( e: Expr, p: Int ): Doc = e match {
    case Apps( Const( "+", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.plusMinus, "+" )
    case Apps( Const( "-", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.plusMinus, "-" )
    case Apps( Const( "*", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.timesDiv, "*" )

    case Neg( Atom( Const( n, _, _ ), Seq( a, b ) ) ) if relOps contains n =>
      binExpr( a, b, p - 3, prio.infixRel, "\\not " + relOps( n ) )
    case Atom( Const( n, _, _ ), Seq( a, b ) ) if relOps contains n =>
      binExpr( a, b, p - 3, prio.infixRel, relOps( n ) )

    case Iff( a, b ) =>
      binExpr( a, b, p, prio.bicond, "\\leftrightarrow" )

    case n: VarOrConst => escapeName( n.name )

    case Top()         => "\\top"
    case Bottom()      => "\\bot"
    case Neg( f )      => ( "\\neg" </> expr( f, prio.quantOrNeg + 1 ) ).group
    case And( a, b )   => binExpr( a, b, p, prio.conj, "\\land" )
    case Or( a, b )    => binExpr( a, b, p, prio.disj, "\\lor" )
    case Imp( a, b )   => binExpr( a, b, p, prio.impl, "\\to" )

    case All( v, f )   => quant( f, v, p, "\\forall" )
    case Ex( v, f )    => quant( f, v, p, "\\exists" )

    case Abs( v, f )   => parenIf( p, prio.lam, "\\lambda" <+> escapeName( v.name ) <> "\\:" </> expr( f, prio.lam + 1 ) ).group

    case IteratedUnaryFunction( f, n, arg ) if n > 1 =>
      "{" <> expr( f, prio.app ).group.nest( 2 ) <> "}^{" <> n.toString <> "}(" <>
        expr( arg, prio.max ).group.nest( 2 ) <> ")"
    case Apps( hd, args ) =>
      expr( hd, prio.app ) <> ( "(" <> Doc.wordwrap2( args.map( expr( _, prio.max ) ), "," ) <> ")" ).nest( 2 ).group
  }

  private object IteratedUnaryFunction {
    private def decompose( expr: Expr, hd: VarOrConst, n: Int ): ( VarOrConst, Int, Expr ) =
      expr match {
        case App( `hd`, arg ) => decompose( arg, hd, n + 1 )
        case _                => ( hd, n, expr )
      }
    def unapply( expr: Expr ): Option[( VarOrConst, Int, Expr )] =
      expr match {
        case App( hd: VarOrConst, arg ) => Some( decompose( arg, hd, 1 ) )
        case _                          => None
      }
  }

  private val escapes = Map(
    '~' -> "\\sim", '∈' -> "\\in", '⊆' -> "\\subseteq", '∪' -> "\\cup", '∩' -> "\\cap", '≤' -> "\\leq",

    '⊥' -> "\\bot", '⊤' -> "\\top",
    '¬' -> "\\neg",
    '∧' -> "\\land", '∨' -> "\\lor", '⊃' -> "\\supset",
    '∀' -> "\\forall", '∃' -> "\\exists",

    'α' -> "\\alpha",
    'β' -> "\\beta",
    'Γ' -> "\\Gamma",
    'γ' -> "\\gamma",
    'Δ' -> "\\Delta",
    'δ' -> "\\delta",
    'ε' -> "\\epsilon",
    'ζ' -> "\\zeta",
    'η' -> "\\eta",
    'Θ' -> "\\Theta",
    'θ' -> "\\theta",
    'ι' -> "\\iota",
    'κ' -> "\\kappa",
    'Λ' -> "\\Lambda",
    'λ' -> "\\lambda",
    'μ' -> "\\mu",
    'ν' -> "\\nu",
    'Ξ' -> "\\Xi",
    'ξ' -> "\\xi",
    'ο' -> "o",
    'Π' -> "\\Pi",
    'π' -> "\\pi",
    'ρ' -> "\\rho",
    'Ρ' -> "\\Rho",
    'Σ' -> "\\Sigma",
    'σ' -> "\\sigma",
    //    'ς" =>"\\sigma",
    'τ' -> "\\tau",
    'Υ' -> "\\Upsilon",
    'υ' -> " \\upsilon ",
    'Φ' -> "\\Phi",
    'φ' -> "\\varphi",
    'Χ' -> "\\Chi",
    'χ' -> "\\chi",
    'Ψ' -> "\\Psi",
    'ψ' -> "\\psi",
    'Ω' -> "\\Omega",
    'ω' -> "\\omega",

    '\\' -> "\\backslash",

    '-' -> "\\text{-}",
    '_' -> "\\_" )
  private val indexedName = """(.*)_(\d+)""".r
  def escapeName( s: String ): String = s match {
    case indexedName( prefix, index ) => s"{${escapeName( prefix )}}_{$index}"
    case _ =>
      s.flatMap( c => escapes.get( c ).fold( c.toString )( " " + _ + " " ) )
  }

  private def apply( ty: Ty, prio: Int ): Doc = ty match {
    case TArr( t, s )   => parenIf( prio, 0, apply( t, 0 ) <+> "\\rightarrow" </> apply( s, 1 ) )
    case TVar( t )      => escapeName( "?" + t )
    case TBase( t, ps ) => Doc.wordwrap2( escapeName( t ) :: ps.map( apply( _, 0 ) ) )
  }
  def apply( ty: Ty ): Doc = apply( ty, 2 )

  // Proofs

  private def inferences[P <: SequentProof[Formula, P]]( p: P ): String = {
    val commandName = p.immediateSubProofs.size match {
      case 0 => "UnaryInfC"
      case 1 => "UnaryInfC"
      case 2 => "BinaryInfC"
      case 3 => "TernaryInfC"
      case 4 => "QuaternaryInfC"
      case 5 => "QuinaryInfC"
    }
    val subProofInfs = if ( p.immediateSubProofs.isEmpty )
      "\\AxiomC{}"
    else
      p.immediateSubProofs.map( inferences( _ ) ).mkString( "\n" )
    s"""$subProofInfs
       |\\RightLabel{$$${escapeName( p.name )}$$}
       |\\$commandName{$$${apply( p.conclusion )}$$}""".stripMargin
  }
  def apply[P <: SequentProof[Formula, P]]( p: P ): String =
    documentWrapper(
      s"""\\begin{prooftree}
       |${inferences( p )}
       |\\end{prooftree}""".stripMargin,
      "\\usepackage{bussproofs}" )

  // LaTeX documents

  private def documentWrapper( body: String, extraPreamble: String = "" ) =
    s"""
     |\\documentclass[a4paper,10pt,landscape]{scrartcl}
     |\\usepackage[margin=1cm]{geometry}
     |$extraPreamble
     |\\begin{document}
     |$body
     |\\end{document}
   """.stripMargin

}
