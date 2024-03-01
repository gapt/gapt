package gapt.provers.viper.aip.axioms
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.flatSubterms
import gapt.expr.formula.hol.instantiate
import gapt.expr.formula.hol.universalClosure
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.LabelledSequent
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.provers.viper.aip.ThrowsError

case object UntrustedFunctionalInductionAxioms extends AxiomFactory {
  def generateScheme( eqns: Vector[( Const, List[Formula], Expr, Expr )] ): Formula = {
    val nameGen = rename.awayFrom( freeVariables( eqns.flatMap( _._2 ) ++ eqns.map( _._3 ) ) )
    val fn @ Const( _, FunctionType( retType, argTypes ), _ ) = eqns.head._1: @unchecked

    val motive = Var( nameGen.fresh( "X" ), FunctionType( To, retType +: argTypes ) )

    val conclusionArgs = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x_$i", t )
    val conclusion = All.Block( conclusionArgs, motive( fn( conclusionArgs ) +: conclusionArgs ) )

    val premises = eqns.map {
      case ( c, conds, lhs @ Apps( _, lhsArgs ), rhs ) =>
        val fvs = freeVariables( lhs +: conds :+ rhs )
        val indHyps = flatSubterms( rhs ).collect {
          case recOcc @ Apps( `c`, recOccArgs ) => motive( recOcc +: recOccArgs )
        }
        All.Block( fvs.toSeq, And( conds ++ indHyps ) --> motive( rhs +: lhsArgs ) )
    }

    All( motive, And( premises ) --> conclusion )
  }

  def guessSchemes( sequent: HOLSequent )( implicit ctx: Context ): Map[Const, Formula] =
    Map() ++ sequent.antecedent.collect {
      case All.Block( vs, Imp.Block( conds, Eq( lhs @ Apps( c: Const, _ ), rhs ) ) ) =>
        ( c, conds, lhs, rhs )
    }.groupBy( _._1 ).view.mapValues( generateScheme ).toMap

  override def apply( sequent: LabelledSequent )( implicit ctx: Context ): ThrowsError[List[Axiom]] = {
    val schemes = guessSchemes( sequent.map( _._2 ) )

    val All.Block( _, goal ) = sequent.succedent.headOption.map( _._2 ).getOrElse( Top() )
    val inductionFormulaInstances =
      schemes.flatMap {
        case ( defConst, indScheme ) =>

          val motives =
            flatSubterms( goal ).collect {
              case t @ Apps( `defConst`, args ) =>
                val nameGen = rename.awayFrom( freeVariables( goal ) )
                val repl = Vector( t -> Var( nameGen.fresh( "z" ), t.ty ) ) ++
                  args.map( arg => arg -> Var( nameGen.fresh( "z" ), arg.ty ) )
                val matrix = TermReplacement( goal, repl.toMap )
                Abs.Block(
                  repl.map( _._2 ),
                  All.Block( freeVariables( matrix ) -- repl.map( _._2 ) toSeq, matrix ) )
            }

          motives.map( instantiate( indScheme, _ ) )
            .map( BetaReduction.betaNormalize )
            .map( universalClosure( _ ) )
      }

    println( inductionFormulaInstances ++: Sequent() )

    Right(
      List() ++ inductionFormulaInstances.map { inst =>
        new Axiom {
          override def formula: Formula = inst
          override def proof: LKProof = ProofLink( FOLConst( "functional_induction" ), Sequent() :+ inst )
        }
      } )
  }
}
