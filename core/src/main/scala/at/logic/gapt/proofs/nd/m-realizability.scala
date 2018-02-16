package at.logic.gapt.proofs.nd

import at.logic.gapt.expr.{ App, typeVariables, Ty, _ }
import at.logic.gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._
import at.logic.gapt.utils.NameGenerator

object MRealizability {

  implicit var systemT: Context = Context.empty

  def setSystemT( ctx: Context ): Unit = {

    systemT = ctx

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
  }

  def mrealize( proof: NDProof )( implicit ctx: Context ): Expr = {

    setSystemT( ctx )

    mrealizeCases( proof )

  }

  def mrealizeCases( proof: NDProof ): Expr = {

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
        val realizerAOrB = App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"natRec(${
            App( mrealizeCases( middleSubProof ), freeVariables( middleSubProof.conclusion ).toSeq ++ insertIndex( variablesAntPremise( proof, 1 ), aux1,
              App( le"pi1(pi2($realizerAOrB))", le"i" ) ) )
          },${
            Abs( Var( "z", ty"nat" ), Abs(
              Var( "z", flat( proof.conclusion.succedent( 0 ) ) ),
              App( mrealizeCases( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ insertIndex( variablesAntPremise( proof, 2 ), aux2,
                App( le"pi2(pi2($realizerAOrB))", Abs( Var( "z", ty"1" ), le"i" ) ) ) ) ) )
          },pi1($realizerAOrB))" )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pair(0,pair(${
            Abs( Var( "z", ty"1" ), App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )
          }, ${
            Abs( Var( "z", ty"1>1" ), Var( "z", flat( rightDisjunct ) ) )
          }))" )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pair(s(0),pair(${
            Abs( Var( "z", ty"1" ), Var( "z", flat( leftDisjunct ) ) )
          }, ${
            Abs( Var( "z", ty"1 > 1" ), App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )
          }))" )

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
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App(
            App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ),
            App( mrealizeCases( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ) ) ) )

      case NegIntroRule( subProof, aux ) =>
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        Abs( freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ), Abs(
          extraVar,
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) ) ) )

      case TopIntroRule() =>
        val varr = Var( "z", ty"1" )
        Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        Abs( freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ), Var( "z", flat( mainFormula ) ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ) :+ eigenVariable,
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) ) )

      case ForallElimRule( subProof, term ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) :+ term ) )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          le"pair($term,${App( mrealizeCases( subProof ), freeVariables( subProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})" )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        Abs( freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ), App(
          mrealizeCases( rightSubProof ),
          freeVariables( rightSubProof.conclusion ).toSeq.map {
            case `eigenVariable` =>
              le"pi1(${App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})"
            case x => x
          } ++ insertIndex( variablesAntPremise( proof, 1 ), aux,
            le"pi2(${App( mrealizeCases( leftSubProof ), freeVariables( leftSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )})" ) ) )

      // only to be used when mainFormula is an equation
      case TheoryAxiom( mainFormula ) =>
        Abs( freeVariables( mainFormula ).toSeq, le"i : 1" )

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        Abs(
          freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ),
          App( mrealizeCases( rightSubProof ), freeVariables( rightSubProof.conclusion ).toSeq ++ variablesAntPremise( proof, 1 ) ) )

      case EqualityIntroRule( term ) =>
        Abs( freeVariables( proof.conclusion ).toSeq, le"i" )

      // Works only for the type of natural numbers at the moment
      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val extraVar = Var( "z", flat( proof.conclusion( Suc( 0 ) ) ) )
        val mrealizerBaseCase = App( mrealizeCases( cases( 0 ).proof ), freeVariables( cases( 0 ).proof.conclusion ).toSeq ++ variablesAntPremise( proof, 0 ) )
        val mrealizerInductionCase = Abs( cases( 1 ).eigenVars :+ extraVar, App(
          mrealizeCases( cases( 1 ).proof ),
          freeVariables( cases( 1 ).proof.conclusion ).toSeq ++ insertIndex( variablesAntPremise( proof, 1 ), cases( 1 ).hypotheses( 0 ), extraVar ) ) )
        Abs( freeVariables( proof.conclusion ).toSeq ++ variablesAntConclusion( proof ), le"natRec($mrealizerBaseCase,$mrealizerInductionCase,$term)" )

      // assuming that the defintionrule is applied according to rewrite rules of the original context
      case DefinitionRule( subProof, mainFormula ) =>
        mrealizeCases( subProof )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
    } )
  }

  def flat( formula: Formula ): Ty = formula match {
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
  def removeEmptyProgram( term: Expr ): Expr = {

    val empty = hoc"i"
    val emptyType = ty"1"

    term match {
      case Var( name, typee ) =>
        if ( removeEmptyProgramType( typee ) == emptyType ) empty
        else Var( name, removeEmptyProgramType( typee ) )
      case Const( "natRec", _, params ) => {
        val parameter = removeEmptyProgramType( params.head )
        if ( parameter == emptyType ) empty
        else Const( "natRec", parameter ->: ( ty"nat" ->: parameter ->: parameter ) ->: ty"nat" ->: parameter, List( parameter ) )
      }
      case Abs( variable, termm ) => {
        if ( removeEmptyProgram( termm ) == empty ) empty
        else if ( removeEmptyProgramType( variable.ty ) == emptyType ) removeEmptyProgram( termm )
        else Abs( Var( variable.name, removeEmptyProgramType( variable.ty ) ), removeEmptyProgram( termm ) )
      }
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
      case App( term1, term2 ) => {
        if ( removeEmptyProgram( term1 ) == empty ) empty
        else if ( removeEmptyProgram( term2 ) == empty ) removeEmptyProgram( term1 )
        else App( removeEmptyProgram( term1 ), removeEmptyProgram( term2 ) )
      }
      case _ => term
    }
  }

  // similar but for types
  def removeEmptyProgramType( typee: Ty ): Ty = {

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