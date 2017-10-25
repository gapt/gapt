package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ ->, Const, Expr, TBase, Ty }
import at.logic.gapt.proofs.Context.InductiveType

object IsKSimple {
  def apply( proof: LKProof ): Boolean = {
    val base: Ty = TBase( "nat", List() )
    val successor: Const = Const( "s", ->( base, base ) )
    val zero: Const = Const( "0", base )
    val nat = InductiveType( base, zero, successor )
    val inducProofs = proof.subProofs.collect { case p: InductionRule if p.indTy == nat.ty => p}
    (for (p <- inducProofs; c <- p.cases  if c.constructor.name == "s") yield (c.eigenVars, p.term)).foldRight( (true, Const("",TBase("nat")).asInstanceOf[Expr] ))( ( a, z ) =>
      if(a._1.contains( a._2 ) && z._2.equals( Const("",TBase("nat"))))   (z._1,a._2)
      else (a._1.contains( a._2 ) && a._2 == z._2 && z._1, z._2))._1
  }

}

