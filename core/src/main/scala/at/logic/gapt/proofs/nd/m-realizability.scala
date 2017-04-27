package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

object MRealizability {

  def mrealize( proof: NDProof ): Expr = proof match {
    case WeakeningRule( subProof, formula ) =>
      BetaReduction.betaNormalize(
        Abs(
          ( freeVars( proof ) :+ Var( "z", flat( formula ) ) ) ++ assumptions( subProof.conclusion ),
          App( mrealize( subProof ), freeVars( subProof ) ++ assumptions( subProof.conclusion ) )
        )
      )

    case ContractionRule( subProof, aux1, aux2 ) =>
      BetaReduction.betaNormalize(
        Abs(
          ( freeVars( proof ) :+ Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) ++ assumptions( subProof.conclusion.delete( aux1, aux2 ) ),
          App( mrealize( subProof ), ( ( freeVars( subProof ) :+
            Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) :+
            Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) ++
            assumptions( subProof.conclusion.delete( aux1, aux2 ) ) )
        )
      )

    case LogicalAxiom( formula ) =>
      Abs( freeVars( proof ) :+ Var( "x", flat( formula ) ), Var( "x", flat( formula ) ) )

    case AndElim1Rule( subProof ) =>
      BetaReduction.betaNormalize(
        Abs(
          freeVars( proof ) ++ assumptions( proof.conclusion ),
          proj1( App( mrealize( subProof ), freeVars( subProof ) ++ assumptions( subProof.conclusion ) ) )
        )
      )

    case AndElim2Rule( subProof ) =>
      BetaReduction.betaNormalize(
        Abs(
          freeVars( proof ) ++ assumptions( proof.conclusion ),
          proj2( App( mrealize( subProof ), freeVars( subProof ) ++ assumptions( subProof.conclusion ) ) )
        )
      )

    case AndIntroRule( leftSubproof, rightSubproof ) =>
      BetaReduction.betaNormalize(
        Abs(
          freeVars( proof ) ++ assumptions( proof.conclusion ),
          pair(
            App( mrealize( leftSubproof ), freeVars( leftSubproof ) ++ assumptions( leftSubproof.conclusion ) ),
            App( mrealize( rightSubproof ), freeVars( rightSubproof ) ++ assumptions( rightSubproof.conclusion ) )
          )
        )
      )

    case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case OrIntro1Rule( subProof, rightDisjunct ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case OrIntro2Rule( subProof, leftDisjunct ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ImpElimRule( leftSubProof, rightSubProof ) =>
      Abs(
        freeVars( proof ) ++ assumptions( proof.conclusion ),
        App(
          App( mrealize( leftSubProof ), freeVars( leftSubProof ) ++ assumptions( leftSubProof.conclusion ) ),
          App( mrealize( rightSubProof ), freeVars( rightSubProof ) ++ assumptions( rightSubProof.conclusion ) )
        )
      )

    case ImpIntroRule( subProof, aux ) =>
      Abs(
        freeVars( proof ) ++ assumptions( proof.conclusion ),
        Abs(
          Var( "z", flat( subProof.conclusion( aux ) ) ),
          App( mrealize( subProof ), ( freeVars( subProof ) :+ Var( "z", flat( subProof.conclusion( aux ) ) ) ) ++ assumptions( subProof.conclusion ) )
        )
      )

    case NegElimRule( leftSubProof, rightSubProof ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case NegIntroRule( subProof, aux ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case TopIntroRule() =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case BottomElimRule( subProof, mainFormula ) =>
      Abs( freeVars( proof ).diff( freeVars( subProof ) ), mrealize( subProof ) )

    case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ForallElimRule( subProof, formula, term, variable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ExistsIntroRule( subProof, formula, term, variable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case TheoryAxiom( mainFormula ) =>
      // match with cases doesn't work..?
      if ( mainFormula == hof"!x !y (s(x) = s(y) -> x = y )" ) Abs( Seq( Var( "x", int ), Var( "y", int ), Var( "z", one ) ), i )
      else if ( mainFormula == hof"!x (s(x) = 0 -> ⊥ )" ) Abs( Seq( Var( "x", int ), Var( "y", one ) ), i )
      else if ( mainFormula == hof"!x x+0 = x" ) Abs( Var( "x", int ), i )
      else if ( mainFormula == hof"!x !y (x + s(y) = s(x + y))" ) Abs( Seq( Var( "x", int ), Var( "y", int ) ), i )
      else if ( mainFormula == hof"!x (x * 0 = 0)" ) Abs( Var( "x", int ), i )
      else if ( mainFormula == hof"!x!y (x * s(y) = (x * y) + x)" ) Abs( Seq( Var( "x", int ), Var( "y", int ) ), i )
      else throw new MRealizerCreationException( proof.longName, s"$mainFormula is not an axiom in Heyting Arithmetic." )

    case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case EqualityIntroRule( term ) =>
      Abs( freeVars( proof ), i )

    case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
  }

  def flat( formula: Formula ): Ty = formula match {
    case Bottom() => one
    case Top() =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Eq( _, _ ) => one
    case Atom( _, _ ) =>
      throw new FlattenException( formula.toString, "Heyting Arithmetic only contains the equality predicate." )
    case And( leftformula, rightformula ) => conj( flat( leftformula ), flat( rightformula ) )
    case Or( _, _ ) =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Imp( leftformula, rightformula ) => flat( leftformula ) -> flat( rightformula )
    case Neg( subformula ) =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Ex( variable, subformula )  => conj( int, flat( subformula ) )
    case All( variable, subformula ) => int -> flat( subformula )
  }

  val one: Ty = TBase( "1", List() )
  val int: Ty = TBase( "int", List() )
  def conj( left: Ty, right: Ty ): Ty = TBase( "^", List( left, right ) )

  val i: Expr = Const( "i", one )
  val zero: Expr = Const( "0", int )
  val suc: Expr = Const( "s", int )
  def recursor( rtype: Ty ): Expr = Const( s"R-$rtype", ( int -> rtype -> rtype ) -> rtype -> int -> rtype )
  def pair( left: Expr, right: Expr ): Expr = Apps( Const( "pair", left.ty -> right.ty -> conj( left.ty, right.ty ) ), left, right )
  def proj1( term: Expr ): Expr = term.ty match {
    case TBase( "^", List( left, right ) ) => App( Const( "proj1", conj( left, right ) -> left ), term )
    case _                                 => throw new IllegalArgumentException( s"Can't project on $term, because it is not of conjunctive type." )
  }
  def proj2( term: Expr ): Expr = term.ty match {
    case TBase( "^", List( left, right ) ) => App( Const( "proj2", conj( left, right ) -> right ), term )
    case _                                 => throw new IllegalArgumentException( s"Can't project on $term, because it is not of conjunctive type." )
  }

  private def freeVars( proof: NDProof ): Seq[Var] =
    freeVariables( proof.conclusion ).toSeq.map( x => Var( x.name, int ) )
  private def assumptions( sequent: Sequent[Formula] ): Seq[Var] =
    sequent.zipWithIndex.antecedent.map( x => Var( s"x${x._2.toInt}", flat( x._1 ) ) )
}

class MRealizerCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

class FlattenException( name: String, message: String ) extends Exception( s"Cannot flatten $name: " + message )