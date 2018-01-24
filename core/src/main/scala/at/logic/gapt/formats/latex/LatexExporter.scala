package at.logic.gapt.formats.latex

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLSequent, SequentProof }

object LatexExporter {

  // Expressions

  def apply( e: Expr ): String = expr( e, prio.max )

  def apply( sequent: HOLSequent ): String =
    sequent.antecedent.map( apply ).mkString( ", " ) + " \\vdash " + sequent.succedent.map( apply ).mkString( ", " )

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
  private def parenIf( enclosingPrio: Int, currentPrio: Int, inside: String ) =
    if ( enclosingPrio <= currentPrio ) s"($inside)" else inside
  private def binExpr( a: Expr, b: Expr, p: Int, newPrio: Int, op: String ) =
    parenIf( p, newPrio, s"${expr( a, newPrio )} $op ${expr( b, newPrio )}" )
  private def quant( f: Expr, v: Var, p: Int, op: String ) =
    parenIf( p, prio.quantOrNeg, s"$op ${escapeName( v.name )}\\: ${expr( f, prio.quantOrNeg + 1 )}" )
  private val relOps = Map( "=" -> "=", "<" -> "<", ">" -> ">", "<=" -> "\\leq", ">=" -> "\\geq" )
  private def expr( e: Expr, p: Int ): String = e match {
    case Apps( Const( "+", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.plusMinus, "+" )
    case Apps( Const( "-", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.plusMinus, "-" )
    case Apps( Const( "*", _, _ ), Seq( a, b ) ) => binExpr( a, b, p, prio.timesDiv, "*" )

    case Neg( Atom( Const( n, _, _ ), Seq( a, b ) ) ) if relOps contains n =>
      binExpr( a, b, p - 3, prio.infixRel, "\\not " + relOps( n ) )
    case Atom( Const( n, _, _ ), Seq( a, b ) ) if relOps contains n =>
      binExpr( a, b, p - 3, prio.infixRel, relOps( n ) )

    case Iff( a, b ) =>
      binExpr( a, b, p, prio.bicond, "\\equiv" )

    case n: VarOrConst => escapeName( n.name )

    case Top()         => "\\top"
    case Bottom()      => "\\bot"
    case Neg( f )      => "\\neg " + expr( f, prio.quantOrNeg + 1 )
    case And( a, b )   => binExpr( a, b, p, prio.conj, "\\land" )
    case Or( a, b )    => binExpr( a, b, p, prio.disj, "\\lor" )
    case Imp( a, b )   => binExpr( a, b, p, prio.impl, "\\supset" )

    case All( v, f )   => quant( f, v, p, "\\forall" )
    case Ex( v, f )    => quant( f, v, p, "\\exists" )

    case Abs( v, f )   => parenIf( p, prio.lam, s"\\lambda ${escapeName( v.name )}\\: ${expr( f, prio.lam + 1 )}" )

    case IteratedUnaryFunction( f, n, arg ) if n > 1 =>
      s"{${expr( f, prio.app )}}^{$n}(${expr( arg, prio.max )})"
    case Apps( hd, args ) => s"${expr( hd, prio.app )}(${args.map( expr( _, prio.max ) ).mkString( ", " )})"
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

    '-' -> "\\text{-}",
    '_' -> "\\_" )
  private val indexedName = """(.*)_(\d+)""".r
  def escapeName( s: String ): String = s match {
    case indexedName( prefix, index ) => s"{${escapeName( prefix )}}_{$index}"
    case _ =>
      s.flatMap( c => escapes.get( c ).fold( c.toString )( " " + _ + " " ) )
  }

  private def apply( ty: Ty, prio: Int ): String = ty match {
    case t ->: s        => parenIf( prio, 0, s"${apply( t, 0 )} \\rightarrow ${apply( s, 1 )}" )
    case TVar( t )      => escapeName( "?" + t )
    case TBase( t, ps ) => ( escapeName( t ) :: ps.map( apply( _, 0 ) ) ).mkString( " " )
  }
  def apply( ty: Ty ): String = apply( ty, 2 )

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
