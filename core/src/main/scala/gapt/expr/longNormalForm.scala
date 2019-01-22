
package gapt.expr

/**
 * If t = λx₁...λxₘ(y u₁ ... uₚ) is a normal term of type T₁ → ... → Tₙ → U, with
 * U atomic and m ≤ n, then its long normal form is the term
 *
 * λx₁...λxₘλxₘ₊₁...λxₙ(y u₁'... uₚ' xₘ₊₁' ... xₙ'),
 *
 * where uᵢ' is the long normal form of uᵢ and xⱼ' is the long normal form of xⱼ.
 *
 * Implemented according to Definition 2.25, Higher-Order Unification and
 * Matching by Gilles Dowek.
 */
object longNormalForm {

  /**
   * Computes the long normal form.
   *
   * @param term A term.
   * @return The long normal form of `term`. Note that η-expansion is applied
   * only to expressions in β-normal form.
   */
  def apply( term: Expr ): Expr = apply( term, List() )
  def apply( term: Expr, disallowedVars: List[Var] ): Expr = term match {

  /**
   * Computes the long normal form.
   *
   * @param term A term.
   * @param disallowedVars Variables that whose names are not allowed for fresh
   * variables.
   * @return The long normal form of `term`.
   */
    case Var( _, exptype ) => exptype match {
      case Ti => term
      case To => term
      case FunctionType( _, args ) => {
        val binders: List[Var] = args.foldRight( List[Var]() )( ( z, acc ) => {
          val newVar = Var( "eta", z ) // Creating a new var of appropriate type
          rename( newVar, disallowedVars ++ acc ) :: acc // Rename if needed
        } )
        val dv = disallowedVars ++ binders
        Abs( binders, App( term, binders.map( ( z => apply( z, dv ) ) ) ) )
      }
    }

    case App( m, n ) => term.ty match {
      case Ti => term
      case To => term
      case FunctionType( _, args ) => {
        val binders: List[Var] = args.foldRight( List[Var]() )( ( z, acc ) => {
          val newVar = Var( "eta", z ) // Creating a new var of appropriate type
          rename( newVar, disallowedVars ++ acc ) :: acc // Rename if needed
        } )
        val dv = disallowedVars ++ binders
        Abs( binders, App( App( m, apply( n, dv ) ), binders.map( ( z => apply( z, dv ) ) ) ) )
      }
    }

    case Abs( x, t ) => Abs( x, apply( t, disallowedVars ) )
  }
}

