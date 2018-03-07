package at.logic.gapt.proofs.nd

import at.logic.gapt.expr.{ App, Ty, typeVariables, _ }
import at.logic.gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import at.logic.gapt.proofs._
import at.logic.gapt.utils.NameGenerator

object ClassicalExtraction {

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
      ( pi1, List( ( pi1( pair( x, y ) ) -> x ) ) ) ) )( systemT )
    systemT += PrimRecFun( List(
      ( pi2, List( ( pi2( pair( x, y ) ) -> y ) ) ) ) )( systemT )

    val sum = ty"sum ?a ?b"
    val inl = hoc"inl{?a ?b}: ?a > (sum ?a ?b)"
    val inr = hoc"inr{?a ?b}: ?b > (sum ?a ?b)"
    systemT += InductiveType( sum, inl, inr )

    val matchSum = hoc"matchSum{?a ?b ?c}: (sum ?a ?b) > (?a > ?c) > (?b > ?c) > ?c"
    val w1: Expr = hov"w1: ?a > ?c"
    val w2: Expr = hov"w2: ?b > ?c"
    systemT += PrimRecFun( List(
      ( matchSum, List(
        ( matchSum( inl( x ), w1, w2 ) -> w1( x ) ),
        ( matchSum( inr( y ), w1, w2 ) -> w2( y ) ) ) ) ) )( systemT )

    val exn = ty"exn ?a"
    val exception = hoc"exception{?a}: ?a > (exn ?a)"
    systemT += InductiveType( exn, exception )
    val raise = hoc"raise{?a ?b}: (exn ?a) > ?b"
    systemT += raise
    /*
    val e: Expr = Var( "e", exn )
    systemT += PrimRecFun( List(
      ( raise, List(
        //( raise( e )( y ) -> raise( e ) ) ) ) ) )( systemT )
        ( raise( raise( e ) ) -> raise( e ) ) ) ) ) )( systemT )
    */

    val handle = hoc"handle{?a ?b}: ((exn ?a) > ?b) > (?a > ?b) > ?b"
    systemT += handle

    // add a term+type to represent the empty program
    systemT += InductiveType(
      ty"1",
      hoc"i : 1" )

    systemT
  }

  def mrealize( proof: NDProof, re: Boolean = true )( implicit ctx: Context ): Expr = {

    val context = systemT( ctx )
    val mrealizer = mrealizeCases( proof )( context )

    if ( re ) removeEmptyProgram( mrealizer )( context ) else mrealizer
  }

  def mrealizeCases( proof: NDProof )( implicit systemT: Context ): Expr = {

    BetaReduction.betaNormalize( proof match {
      case WeakeningRule( subProof, formula ) =>
        Abs( variablesAntConclusion( proof ), App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) ) )

      case ContractionRule( subProof, aux1, aux2 ) =>
        Abs( variablesAntConclusion( proof ), App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) ) )

      case LogicalAxiom( formula ) =>
        Abs( Var( "x", flat( formula ) ), Var( "x", flat( formula ) ) )

      case AndElim1Rule( subProof ) =>
        Abs( variablesAntConclusion( proof ), le"pi1(${App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) )})" )

      case AndElim2Rule( subProof ) =>
        Abs( variablesAntConclusion( proof ), le"pi2(${App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) )})" )

      case AndIntroRule( leftSubproof, rightSubproof ) =>
        Abs(
          variablesAntConclusion( proof ),
          le"pair(${App( mrealizeCases( leftSubproof ), variablesAntPremise( proof, 0 ) )},${App( mrealizeCases( rightSubproof ), variablesAntPremise( proof, 1 ) )})" )

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        Abs(
          variablesAntConclusion( proof ),
          le"""matchSum
            ${App( mrealizeCases( leftSubProof ), variablesAntPremise( proof, 0 ) )}
            ${App( mrealizeCases( middleSubProof ), variablesAntPremise( proof, 1 ) )}
            ${App( mrealizeCases( rightSubProof ), variablesAntPremise( proof, 2 ) )}
          """ )

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        val leftType = flat( subProof.endSequent( Suc( 0 ) ) )
        val rightType = flat( rightDisjunct )
        val inl = systemT.constant( "inl", List( leftType, rightType ) ).get
        Abs( variablesAntConclusion( proof ), inl( App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) ) ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        val leftType = flat( leftDisjunct )
        val rightType = flat( subProof.endSequent( Suc( 0 ) ) )
        val inr = systemT.constant( "inr", List( leftType, rightType ) ).get
        Abs( variablesAntConclusion( proof ), inr( App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) ) ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        Abs(
          variablesAntConclusion( proof ),
          App( App( mrealizeCases( leftSubProof ), variablesAntPremise( proof, 0 ) ), App( mrealizeCases( rightSubProof ), variablesAntPremise( proof, 1 ) ) ) )

      case ImpIntroRule( subProof, aux ) =>
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        Abs( variablesAntConclusion( proof ) :+ extraVar, App( mrealizeCases( subProof ), insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        val app1 = App( mrealizeCases( leftSubProof ), variablesAntPremise( proof, 0 ) )
        val app2 = App( mrealizeCases( rightSubProof ), variablesAntPremise( proof, 1 ) )
        Abs(
          variablesAntConclusion( proof ), App( app1, app2 ) )

      case NegIntroRule( subProof, aux ) =>
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        Abs( variablesAntConclusion( proof ) :+ extraVar, le"exception(${App( mrealizeCases( subProof ), insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) )})" )

      case TopIntroRule() =>
        val varr = Var( "z", ty"1" )
        Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        val subProofRealizer = mrealizeCases( subProof )
        // TODO is this true in general?
        val exnTypeParameter = subProofRealizer.ty match {
          case _ ->: _ ->: TBase( "exn", param :: Nil ) => param
          case _                                        => throw new Exception( "Realizer must be of type exn ?a." )
        }
        /*
        val exnTypeParameter = subProofRealizer match {
          case Abs.Block( _, e ) =>
            e.ty match {
              case TBase( "exn", param :: Nil ) => param
              case _                            => throw new Exception( "Realizer must be of type exn ?a." )
            }
        }
        */
        val raisedType = flat( mainFormula )
        val raise = systemT.constant( "raise", List( exnTypeParameter, raisedType ) ).get
        Abs( variablesAntConclusion( proof ), raise( App( subProofRealizer, variablesAntPremise( proof, 0 ) ) ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs( variablesAntConclusion( proof ) :+ eigenVariable, App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) ) )

      case ForallElimRule( subProof, term ) =>
        Abs( variablesAntConclusion( proof ), App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) :+ term ) )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        Abs( variablesAntConclusion( proof ), le"pair($term,${App( mrealizeCases( subProof ), variablesAntPremise( proof, 0 ) )})" )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        Abs( variablesAntConclusion( proof ), App(
          Substitution( eigenVariable, le"pi1(${App( mrealizeCases( leftSubProof ), variablesAntPremise( proof, 0 ) )})" )( mrealizeCases( rightSubProof ) ),
          insertIndex( variablesAntPremise( proof, 1 ), aux, le"pi2(${App( mrealizeCases( leftSubProof ), variablesAntPremise( proof, 0 ) )})" ) ) )

      // only to be used when mainFormula is an equation
      case TheoryAxiom( mainFormula ) =>
        le"i"

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        Abs( variablesAntConclusion( proof ), App( mrealizeCases( rightSubProof ), variablesAntPremise( proof, 1 ) ) )

      case EqualityIntroRule( term ) =>
        le"i"

      // Works only for the type of natural numbers at the moment
      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val extraVar = Var( "z", flat( proof.conclusion( Suc( 0 ) ) ) )
        val mrealizerBaseCase = App( mrealizeCases( cases( 0 ).proof ), variablesAntPremise( proof, 0 ) )
        val mrealizerInductionCase = Abs(
          cases( 1 ).eigenVars :+ extraVar,
          App( mrealizeCases( cases( 1 ).proof ), insertIndex( variablesAntPremise( proof, 1 ), cases( 1 ).hypotheses( 0 ), extraVar ) ) )
        Abs( variablesAntConclusion( proof ), le"natRec($mrealizerBaseCase,$mrealizerInductionCase,$term)" )

      // assuming that the defintionrule is applied according to rewrite rules of the original context
      case DefinitionRule( subProof, mainFormula ) =>
        mrealizeCases( subProof )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        throw new MRealizerCreationException( proof.longName, "This rule is not admitted in Heyting Arithmetic." )
    } )
  }

  def flat( formula: Formula )( implicit systemT: Context ): Ty = formula match {
    case Bottom()                         => ty"1"
    case Top()                            => flat( Imp( Bottom(), Bottom() ) )
    case Eq( _, _ )                       => ty"1"
    case Atom( _, _ )                     => ty"1" // ?
    case And( leftformula, rightformula ) => TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( leftformula, rightformula )  => TBase( "sum", flat( leftformula ), flat( rightformula ) )
    case Imp( leftformula, rightformula ) => flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula )                => flat( subformula ) ->: TBase( "exn", flat( subformula ) )
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

  def insertIndex( sequence: Vector[Var], index: SequentIndex, value: Expr ): Vector[Expr] =
    ( sequence.take( index.toInt.abs - 1 ) :+ value ) ++ sequence.takeRight( sequence.length - ( index.toInt.abs - 1 ) )

  def variablesAntConclusion( proof: NDProof )( implicit systemT: Context ): Vector[Var] = {
    variablesAntConclusionWithIndex( proof ).map( _._2 )
  }

  def variablesAntPremise( proof: NDProof, premiseNumber: Int )( implicit systemT: Context ): Vector[Var] = {
    val positions = proof.occConnectors( premiseNumber ).childrenSequent.antecedent.flatten
    positions.flatMap( variablesAntConclusionWithIndex( proof ).toMap get )
  }

  private def variablesAntConclusionWithIndex( proof: NDProof )( implicit systemT: Context ): Vector[( SequentIndex, Var )] =
    proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( s"x${x._2.toInt}", flat( x._1 ) ) ) )
}

class ClassicalExtractionCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )
