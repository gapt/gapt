package at.logic.gapt.proofs.lk
import at.logic.gapt.expr.{ ->, Const, Expr, TBase, Ty, Var }
import at.logic.gapt.proofs.Context.InductiveType

object IsKSimple {
  def apply( proof: LKProof ): Boolean = {
    val base: Ty = TBase( "nat", List() )
    val successor: Const = Const( "s", ->( base, base ) )
    val zero: Const = Const( "0", base )
    val nat = InductiveType( base, zero, successor )
    val inducProofs: List[LKProof] = proof.subProofs.foldRight( List[LKProof]() )( ( a, z ) => a match {
      case p: InductionRule =>
        if ( p.indTy == nat.ty ) p :: z
        else z
      case _ => z
    } )
    val succ: List[( List[Var], Expr )] = inducProofs.map { a =>
      {
        val InductionRule( c, _, t ) = a
        c.foldRight( ( List[Var](), t ) )( ( b, z ) => {
          b match {
            case InductionCase( _, Const( "s", _ ), _, e, _ ) => ( e.toList, t )
            case _ => z
          }
        } )
      }
    }
    if ( succ.nonEmpty ) succ.foldRight( true )( ( a, z ) => a._1.contains( a._2 ) && a._2 == succ.head._2 && z )
    else true

  }

}

