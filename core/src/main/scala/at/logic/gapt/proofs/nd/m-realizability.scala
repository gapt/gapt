package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._

object MRealizability {

  implicit var systemT = Context()
  systemT += InductiveType(
    ty"conj ?a  ?b",
    hoc"pair: ?a > ?b > conj ?a ?b " )
  systemT += PrimRecFun(
    hoc"pi1: (conj ?a ?b) > ?a",
    "pi1(pair(x,y)) = x" )
  systemT += PrimRecFun(
    hoc"pi2: (conj ?a ?b) > ?b",
    "pi2(pair(x,y)) = y" )
  systemT += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  systemT += PrimRecFun(
    hoc"R: (nat > ?a > ?a) > ?a > nat > ?a",
    "R(x,y,0) = y",
    "R(x,y,s(z)) = x(z,R(x,y,z))" )
  systemT += InductiveType(
    ty"1",
    hoc"i : 1" )

  def mrealize( proof: NDProof ): Expr = normalize( proof match {
    case WeakeningRule( subProof, formula ) =>
      Abs(
        ( freeVariables( proof.conclusion ).toSeq :+ Var( "z", flat( formula ) ) ) ++ variablesAntPremise( proof, 0 ).values,
        App( mrealize( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ).values ) )

    case ContractionRule( subProof, aux1, aux2 ) =>
      Abs(
        ( freeVariables( proof.conclusion ).toSeq :+ Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) ++ variablesAntPremise( proof, 0 ).-( aux1, aux2 ).values,
        App( mrealize( subProof ), ( ( freeVariables( subProof.conclusion ).toSeq :+
          Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) :+
          Var( "z", flat( subProof.conclusion.apply( aux1 ) ) ) ) ++
          variablesAntPremise( proof, 0 ).-( aux1, aux2 ).values ) )

    case LogicalAxiom( formula ) =>
      Abs( freeVariables( proof.conclusion ).toSeq :+ Var( "x", flat( formula ) ), Var( "x", flat( formula ) ) )

    case AndElim1Rule( subProof ) =>
      Abs(
        freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ).values,
        le"pi1(${App( mrealize( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ).values )})" )

    case AndElim2Rule( subProof ) =>
      Abs(
        freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ).values,
        le"pi2(${App( mrealize( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ).values )})" )

    case AndIntroRule( leftSubproof, rightSubproof ) =>
      Abs(
        freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ).values,
        le"pair(${
          App( mrealize( leftSubproof ), freeVariables( leftSubproof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ).values )
        },${
          App( mrealize( rightSubproof ), freeVariables( rightSubproof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ).values )
        })" )

    case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case OrIntro1Rule( subProof, rightDisjunct ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case OrIntro2Rule( subProof, leftDisjunct ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ImpElimRule( leftSubProof, rightSubProof ) =>
      Abs(
        freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ).values,
        App(
          normalize( App( mrealize( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ).values ) ),
          normalize( App( mrealize( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ).values ) ) ) )

    case ImpIntroRule( subProof, aux ) =>
      Abs(
        freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ).values,
        Abs(
          Var( "z", flat( subProof.conclusion( aux ) ) ),
          App( mrealize( subProof ), ( freeVariables( subProof.conclusion ).toSeq :+ Var( "z", flat( subProof.conclusion( aux ) ) ) ) ++ variablesAntPremise( proof, 0 ).values ) ) )

    case NegElimRule( leftSubProof, rightSubProof ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case NegIntroRule( subProof, aux ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case TopIntroRule() =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case BottomElimRule( subProof, mainFormula ) =>
      Abs( freeVariables( proof.conclusion ).toSeq.diff( freeVariables( subProof.conclusion ).toSeq ), mrealize( subProof ) )

    case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ForallElimRule( subProof, variable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ExistsIntroRule( subProof, formula, term, variable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case TheoryAxiom( mainFormula ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
      throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

    case EqualityIntroRule( term ) =>
      Abs( freeVariables( proof.conclusion ).toSeq, le"i" )

    case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
  } )

  def flat( formula: Formula ): Ty = formula match {
    case Bottom() => ty"1"
    case Top() =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Eq( _, _ )                       => ty"1"
    case Atom( _, _ )                     => ty"1"
    case And( leftformula, rightformula ) => TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( _, _ ) =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Imp( leftformula, rightformula ) => flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula ) =>
      throw new FlattenException( formula.toString, "Not implemented yet." )
    case Ex( variable, subformula )  => TBase( "conj", variable.ty, flat( subformula ) )
    case All( variable, subformula ) => variable.ty ->: flat( subformula )
  }

  def variablesAntConclusion( proof: NDProof ): Map[SequentIndex, Var] =
    proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( s"x${x._2.toInt}", flat( x._1 ) ) ) ).toMap

  def variablesAntPremise( proof: NDProof, premiseNumber: Int ): Map[SequentIndex, Var] = {
    val positions = proof.occConnectors( premiseNumber ).childrenSequent.antecedent.flatten
    variablesAntConclusion( proof ).filterKeys( positions.contains( _ ) )
  }

}

class MRealizerCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

class FlattenException( name: String, message: String ) extends Exception( s"Cannot flatten $name: " + message )