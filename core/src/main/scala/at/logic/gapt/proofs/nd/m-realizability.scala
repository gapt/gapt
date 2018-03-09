package at.logic.gapt.proofs.nd

import at.logic.gapt.expr
import at.logic.gapt.expr.{ App, Ty, typeVariables, Substitution, _ }
import at.logic.gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._
import at.logic.gapt.utils.NameGenerator

object MRealizability {

  def systemT( ctx: Context ): Context = {

    implicit var systemT = ctx

    // add recursors for all inductive types
    for ( ( name, constructors ) <- systemT.get[StructurallyInductiveTypes].constructors.filter( _._1 != "o" ) ) {
      val typ = systemT.get[BaseTypes].baseTypes( name )
      val argTypes = constructors.map( x => x -> FunctionType.unapply( x.ty ).get._2 ) toMap
      val resultVariable = TVar( new NameGenerator( typeVariables( typ ) map ( _.name ) ).fresh( "a" ) )
      val ngTermVariableNames = new NameGenerator( systemT.constants map ( _.name ) )

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

      systemT += PrimRecFun( List( ( recursor, equations ) ) )
    }

    // add conjuctive type, pairs, projections and their reduction rules
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

    // add a term+type to represent the empty program
    systemT += InductiveType(
      ty"1",
      hoc"i : 1" )

    systemT
  }

  // Creates a term M for the conclusion of the proof such that:
  // if M1,...,Mk are m-realizers for the formulas in the antecedent,
  // then M[M1/x1]...[Mk/xk] m-realizes the succedent of the conclusion
  def mrealize( proof: NDProof, re: Boolean = true )( implicit ctx: Context ): ( Map[SequentIndex, Var], Expr ) = {

    val context = systemT( ctx )

    val variables = proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( s"x${x._2.toInt}", flat( x._1 ) ) ) ).toMap

    val mrealizer = mrealizeCases( proof, variables )( context )

    if ( re )
      ( variables map ( x => ( x._1, Var( x._2.name, removeEmptyProgramType( x._2.ty )( context ) ) ) ),
        removeEmptyProgram( mrealizer )( context ) )
    else ( variables, mrealizer )
  }

  def mrealizeCases( proof: NDProof, variables: Map[SequentIndex, Var] )( implicit systemT: Context ): Expr = {

    proof match {
      case WeakeningRule( subProof, formula ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) )

      case ContractionRule( subProof, aux1, aux2 ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) )

      case LogicalAxiom( formula ) =>
        variables.head._2

      case AndElim1Rule( subProof ) =>
        le"pi1(${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) )})"

      case AndElim2Rule( subProof ) =>
        le"pi2(${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) )})"

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        le"pair(${mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) )},${mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) )})"

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        val realizerAOrB = mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) )

        val varsA = varsAntPrem( proof, variables, 1 ) + ( aux1 -> Var( "xa", flat( middleSubProof.conclusion( aux1 ) ) ) )
        val varsB = varsAntPrem( proof, variables, 2 ) + ( aux2 -> Var( "xb", flat( rightSubProof.conclusion( aux2 ) ) ) )

        val sub1 = Substitution( varsA( aux1 ), App( le"pi1(pi2($realizerAOrB))", le"i" ) )
        val sub2 = Substitution( varsB( aux2 ), App( le"pi2(pi2($realizerAOrB))", Abs( Var( "c", ty"1" ), le"i" ) ) )

        le"natRec(${
          sub1( mrealizeCases( middleSubProof, varsA ) )
        }, ${
          Abs( Var( "a", ty"nat" ), Abs(
            Var( "b", flat( proof.conclusion.succedent( 0 ) ) ),
            sub2( mrealizeCases( rightSubProof, varsB ) ) ) )
        },pi1($realizerAOrB))"

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        le"pair(0,pair(${
          Abs( Var( "w", ty"1" ), mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) ) )
        }, ${
          Abs( Var( "w", ty"1>1" ), Var( "w0", flat( rightDisjunct ) ) )
        }))"

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        le"pair(s(0),pair(${
          Abs( Var( "v", ty"1" ), Var( "v0", flat( leftDisjunct ) ) )
        }, ${
          Abs( Var( "v", ty"1 > 1" ), mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) ) )
        }))"

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        App(
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) ),
          mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) ) )

      case ImpIntroRule( subProof, aux ) =>
        val extraVar = Var( "h", flat( subProof.conclusion( aux ) ) )
        Abs( extraVar, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        App(
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) ),
          mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) ) )

      case NegIntroRule( subProof, aux ) =>
        val extraVar = Var( "n", flat( subProof.conclusion( aux ) ) )
        Abs( extraVar, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ) ) )

      case TopIntroRule() =>
        val varr = Var( "t", ty"1" )
        Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        Var( "b", flat( mainFormula ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs( eigenVariable, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) ) )

      case ForallElimRule( subProof, term ) =>
        App( mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) ), term )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        le"pair($term,${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) )})"

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val mrealizerLeft = mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) )
        val sub1 = Substitution( eigenVariable, le"pi1($mrealizerLeft)" )
        val varsRight = varsAntPrem( proof, variables, 1 ) + ( aux -> Var( "u", flat( rightSubProof.conclusion( aux ) ) ) )
        val sub2 = Substitution( varsRight( aux ), le"pi2($mrealizerLeft)" )
        sub1( sub2( mrealizeCases( rightSubProof, varsRight ) ) )

      // only to be used when mainFormula is an equation
      case TheoryAxiom( mainFormula ) =>
        le"i"

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) )

      case EqualityIntroRule( term ) =>
        le"i"

      // Works only for the type of natural numbers at the moment
      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val extraVar = Var( "e", flat( proof.conclusion( Suc( 0 ) ) ) )
        val mrealizerBaseCase = mrealizeCases( cases( 0 ).proof, varsAntPrem( proof, variables, 0 ) )
        val mrealizerInductionCase = Abs(
          cases( 1 ).eigenVars :+ extraVar,
          mrealizeCases( cases( 1 ).proof, varsAntPrem( proof, variables, 1 ) + ( cases( 1 ).hypotheses( 0 ) -> extraVar ) ) )
        le"natRec($mrealizerBaseCase,$mrealizerInductionCase,$term)"

      // assuming that the definitionrule is applied according to rewrite rules of the original context
      case DefinitionRule( subProof, mainFormula ) =>
        mrealizeCases( subProof, variables )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
    }
  }

  // computes the type of a potential m-realizer for the formula
  def flat( formula: Formula )( implicit systemT: Context ): Ty = formula match {
    case Bottom()                         => ty"1"
    case Top()                            => flat( Imp( Bottom(), Bottom() ) )
    case Eq( _, _ )                       => ty"1"
    case Atom( _, _ )                     => ty"1" // ?
    case And( leftformula, rightformula ) => TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( leftformula, rightformula )  => flat( Ex( Var( "x", ty"nat" ), And( Imp( Eq( Var( "x", ty"nat" ), le"0" ), leftformula ), Imp( Neg( Eq( Var( "x", ty"nat" ), le"0" ) ), rightformula ) ) ) )
    case Imp( leftformula, rightformula ) => flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula )                => flat( Imp( subformula, Bottom() ) )
    case Ex( variable, subformula )       => TBase( "conj", variable.ty, flat( subformula ) )
    case All( variable, subformula )      => variable.ty ->: flat( subformula )
  }

  // removes all occurences of the empty program i : 1 from term, or is i : 1 itself
  // only for recursors for natural numbers now
  def removeEmptyProgram( term: Expr )( implicit systemT: Context ): Expr = {

    val empty = hoc"i"
    val emptyType = ty"1"

    term match {
      case Var( name, typee ) =>
        if ( removeEmptyProgramType( typee ) == emptyType ) empty
        else Var( name, removeEmptyProgramType( typee ) )
      case Const( "natRec", _, params ) =>
        val parameter = removeEmptyProgramType( params.head )
        if ( parameter == emptyType ) empty
        else Const( "natRec", parameter ->: ( ty"nat" ->: parameter ->: parameter ) ->: ty"nat" ->: parameter, List( parameter ) )
      case Abs( variable, termm ) =>
        if ( removeEmptyProgram( termm ) == empty ) empty
        else if ( removeEmptyProgramType( variable.ty ) == emptyType ) removeEmptyProgram( termm )
        else Abs( Var( variable.name, removeEmptyProgramType( variable.ty ) ), removeEmptyProgram( termm ) )
      case App( App( Const( "pair", conjtype, params ), left ), right ) =>
        if ( removeEmptyProgram( right ) == empty ) removeEmptyProgram( left )
        else if ( removeEmptyProgram( left ) == empty ) removeEmptyProgram( right )
        else App( App( Const( "pair", removeEmptyProgramType( conjtype ), params.map( removeEmptyProgramType( _ ) ) ), removeEmptyProgram( left ) ), removeEmptyProgram( right ) )
      case App( Const( "pi1", TArr( TBase( "conj", typeparams ), termmtype ), params ), termm ) =>
        if ( removeEmptyProgramType( typeparams( 0 ) ) == emptyType ) empty
        else if ( removeEmptyProgramType( typeparams( 1 ) ) == emptyType ) removeEmptyProgram( termm )
        else App( Const( "pi1", TArr( TBase( "conj", typeparams.map( removeEmptyProgramType( _ ) ) ), removeEmptyProgramType( termmtype ) ), params.map( removeEmptyProgramType( _ ) ) ), removeEmptyProgram( termm ) )
      case App( Const( "pi2", TArr( TBase( "conj", typeparams ), termmtype ), params ), termm ) =>
        if ( removeEmptyProgramType( typeparams( 1 ) ) == emptyType ) empty
        else if ( removeEmptyProgramType( typeparams( 0 ) ) == emptyType ) removeEmptyProgram( termm )
        else App( Const( "pi2", TArr( TBase( "conj", typeparams.map( removeEmptyProgramType( _ ) ) ), removeEmptyProgramType( termmtype ) ), params.map( removeEmptyProgramType( _ ) ) ), removeEmptyProgram( termm ) )
      case App( term1, term2 ) =>
        if ( removeEmptyProgram( term1 ) == empty ) empty
        else if ( removeEmptyProgram( term2 ) == empty ) removeEmptyProgram( term1 )
        else App( removeEmptyProgram( term1 ), removeEmptyProgram( term2 ) )
      case _ => term
    }
  }

  // similar but for types
  def removeEmptyProgramType( typee: Ty )( implicit systemT: Context ): Ty = {

    val empty = ty"1"

    typee match {
      case TBase( "conj", params ) =>
        if ( removeEmptyProgramType( params( 0 ) ) == empty ) removeEmptyProgramType( params( 1 ) )
        else if ( removeEmptyProgramType( params( 1 ) ) == empty ) removeEmptyProgramType( params( 0 ) )
        else TBase( "conj", removeEmptyProgramType( params( 0 ) ), removeEmptyProgramType( params( 1 ) ) )
      case TArr( in, out ) =>
        if ( removeEmptyProgramType( out ) == empty ) empty
        else if ( removeEmptyProgramType( in ) == empty ) removeEmptyProgramType( out )
        else TArr( removeEmptyProgramType( in ), removeEmptyProgramType( out ) )
      case _ => typee
    }
  }

  // Given a proof and variables for the formulas in the antecedent of the conlusion,
  // returns those variables that occur as well in the antecedent of the conclusion of the premise at premisenumber.
  def varsAntPrem( proof: NDProof, varsAntConcl: Map[SequentIndex, Var], premiseNumber: Int ): Map[SequentIndex, Var] = {
    val positions: Vector[( Seq[SequentIndex], SequentIndex )] = proof.occConnectors( premiseNumber ).childrenSequent.zipWithIndex.antecedent
    val variables: Vector[( Seq[Option[Var]], SequentIndex )] = positions.map( x => ( x._1.map( y => varsAntConcl.get( y ) ), x._2 ) )
    val flattened: Vector[( Seq[Var], SequentIndex )] = variables.map( x => ( x._1.flatten, x._2 ) )
    flattened.flatMap( x => x._1.map( y => ( x._2, y ) ) ).toMap
  }

}

class MRealizerCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

class FlattenException( name: String, message: String ) extends Exception( s"Cannot flatten $name: " + message )