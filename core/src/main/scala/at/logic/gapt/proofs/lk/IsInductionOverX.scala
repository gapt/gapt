package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ Abs, Const, Expr, ExprSubstitutable1, Substitutable, Substitution, Var, freeVariables }
import at.logic.gapt.proofs.Context.InductiveType

object IsInductionOverX {
  def apply( proof: LKProof, arg: InductiveType ): Boolean =
    proof.subProofs.forall {
      case p: InductionRule => {
        println( "induction stuff   " + p.term.toString() + "  " + p.formula.toString() )
        println( "induction cases  " + p.cases.head.eigenVars + "  " + p.cases.tail.head.eigenVars )
        p.indTy == arg.ty
      }
      case _ => true
    }
}

object InductiveSubProof {
  def apply( proof: LKProof ): List[LKProof] =
    proof.subProofs.toList.foldRight( List[LKProof]() )( ( a, z ) => {
      a match {
        case p: InductionRule => {
          val succ: Var = p.cases.foldRight( Var( "wrong", p.indTy ): Var )( ( a, z ) => {
            a match {
              case InductionCase( _, Const( "s", _ ), _, e, _ ) => e.head
              case _ => z
            }
          } )
          val ret: Expr = Substitution( freeVariables( p.formula.term ).head -> succ )( p.formula.term )
          println( "This is the formula   " + p.term + " and " + ret )
          InductionRule( p.cases, Abs( succ, ret ), succ ) :: z
        }
        case _ => z
      }
    } )

}
