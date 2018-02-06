package at.logic.gapt.proofs.nd

import at.logic.gapt.expr.{ App, typeVariables, _ }
import at.logic.gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._
import at.logic.gapt.utils.NameGenerator

object MRealizability {

  def addRecursors( implicit ctx: Context ): Context = {
    var ctxx = Context.empty

    for ( ( name, constructors ) <- ctx.get[StructurallyInductiveTypes].constructors.filter( _._1 != "o" ) ) {
      val typ = ctx.get[BaseTypes].baseTypes( name )
      ctxx += InductiveType( typ, constructors )
      val argTypes = constructors.map( x => x -> FunctionType.unapply( x.ty ).get._2 ) toMap
      val resultVariable = TVar( new NameGenerator( typeVariables( typ ) map ( _.name ) ).fresh( "a" ) )
      val ngTermVariableNames = new NameGenerator( ctx.constants map ( _.name ) )

      val constrVars = constructors.map( x => x -> Var(
        ngTermVariableNames.fresh( "x" ),
        argTypes( x ).foldRight( resultVariable: Ty )( ( y, z ) => if ( y == typ ) typ ->: resultVariable ->: z else y ->: z ) ) ) toMap

      val recursortype = constructors.foldRight( typ ->: resultVariable: Ty )( ( x, y ) => constrVars( x ).ty ->: y )
      val recursor = Const( name + "Rec", recursortype, typeVariables( recursortype ).toList )
      val argVars = argTypes.map( x => x._1 -> x._2.map( y => Var( ngTermVariableNames.fresh( "x" ), y ) ) )

      val equations = constructors.map( x =>
        (
          App( recursor, constrVars.values.toVector :+ App( x, argVars( x ) ) ),
          argVars( x ).foldLeft( constrVars( x ): Expr )( ( y, z ) => if ( z.ty == typ ) App( App( y, z ), App( recursor, constrVars.values.toVector :+ z ) ) else App( y, z ) ) ) )

      ctxx += PrimRecFun( List( ( recursor, equations ) ) )
    }
    ctxx
  }

  def mrealize( proof: NDProof )( implicit ctx: Context ): Expr = {

    var systemT = addRecursors( ctx )

    val a = TVar( "a" )
    val b = TVar( "b" )
    val conj = TBase( "conj", a, b )
    val pair = Const( "pair", a ->: b ->: conj, List( a, b ) )
    systemT += InductiveType( conj, pair )

    val pi1 = Const( "pi1", conj ->: a, List( a, b ) )
    val pi2 = Const( "pi2", conj ->: b, List( a, b ) )
    val x: Expr = Var( "x", a )
    val y: Expr = Var( "y", b )
    systemT += PrimRecFun( List(
      ( pi1, List(
        ( App( pi1, App( pair, List( x, y ) ) ), x ) ) ) ) )( systemT )
    systemT += PrimRecFun( List(
      ( pi2, List(
        ( App( pi2, App( pair, List( x, y ) ) ), y ) ) ) ) )( systemT )

    /*systemT += InductiveType(
      ty"conj ?a  ?b",
      hoc"pair{?a ?b}: ?a > ?b > conj ?a ?b " )
    systemT += PrimRecFun(
      hoc"pi1{?a ?b}: (conj ?a ?b) > ?a",
      "pi1(pair(x,y)) = x" )
    systemT += PrimRecFun(
      hoc"pi2{?a ?b}: (conj ?a ?b) > ?b",
      "pi2(pair(x,y)) = y" )*/

    systemT += InductiveType(
      ty"1",
      hoc"i : 1" )

    mrealizeCases( proof )( systemT )
  }

  def mrealizeCases( proof: NDProof )( implicit ctx: Context ): Expr = {

    normalize( proof match {
      case WeakeningRule( subProof, formula ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )

      case ContractionRule( subProof, aux1, aux2 ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )

      case LogicalAxiom( formula ) =>
        Abs( freeVariables( proof.conclusion ).toSeq :+ Var( "x", flat( formula ) ), Var( "x", flat( formula ) ) )

      case AndElim1Rule( subProof ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pi1(${App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})" )

      case AndElim2Rule( subProof ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pi2(${App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})" )

      case AndIntroRule( leftSubproof, rightSubproof ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pair(${
            App( mrealizeCases( leftSubproof ), freeVariables( leftSubproof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )
          },${
            App( mrealizeCases( rightSubproof ), freeVariables( rightSubproof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ) )
          })" )

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App(
            App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ),
            App( mrealizeCases( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ) ) ) )

      case ImpIntroRule( subProof, aux ) =>
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          Abs(
            extraVar,
            App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case NegIntroRule( subProof, aux ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case TopIntroRule() =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case BottomElimRule( subProof, mainFormula ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ) :+ eigenVariable,
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )

      case ForallElimRule( subProof, variable ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        Abs( freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ), App(
          mrealizeCases( rightSubProof ),
          freeVariables( rightSubProof.conclusion ).toSeq.map {
            case `eigenVariable` =>
              le"pi1(${App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})"
            case x => x
          } ++ insertIndex( variablesAntPremise( proof, 1 ), aux,
            le"pi2(${App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})" ) ) )

      case TheoryAxiom( mainFormula ) =>
        throw new MRealizerCreationException( proof.longName, "Not implemented yet." )

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App( mrealizeCases( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ) ) )

      case EqualityIntroRule( term ) =>
        Abs( freeVariables( proof.conclusion ).toSeq, le"i" )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
    } )
  }

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

  def insertIndex( sequence: Vector[Var], index: SequentIndex, value: Expr ): Vector[Expr] =
    ( sequence.take( index.toInt.abs - 1 ) :+ value ) ++ sequence.takeRight( sequence.length - ( index.toInt.abs - 1 ) )

  def variablesAntConclusion( proof: NDProof ): Vector[Var] = {
    variablesAntConclusionWithIndex( proof ).map( _._2 )
  }

  def variablesAntPremise( proof: NDProof, premiseNumber: Int ): Vector[Var] = {
    val positions = proof.occConnectors( premiseNumber ).childrenSequent.antecedent.flatten
    positions.flatMap( variablesAntConclusionWithIndex( proof ).toMap get )
  }

  private def variablesAntConclusionWithIndex( proof: NDProof ): Vector[( SequentIndex, Var )] =
    proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( s"x${x._2.toInt}", flat( x._1 ) ) ) )
}

class MRealizerCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

class FlattenException( name: String, message: String ) extends Exception( s"Cannot flatten $name: " + message )