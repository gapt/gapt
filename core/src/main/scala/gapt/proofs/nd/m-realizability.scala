package gapt.proofs.nd

import gapt.expr.App
import gapt.expr.Var
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TArr
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.expr.util.freeVariables
import gapt.expr.util.typeVariables
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.utils.NameGenerator

object MRealizability {

  /**
   * Gives a recursor constant for an inductive type.
   *
   * @param indType the inductive type that the recursor is for
   * @param resultType type of the result of applying terms to the recursor
   * @param ctx context that the inductive type is defined in
   * @return recursor constant
   */
  def recursor( indType: TBase, resultType: Ty )( implicit ctx: Context ): Const = {
    val Some( constructors ) = ctx.getConstructors( indType )
    val recTypes = constructors.map {
      case constr @ Const( _, FunctionType( _, constrArgTypes ), _ ) =>
        FunctionType( resultType, constrArgTypes.flatMap( argType => if ( argType == indType ) Seq( indType, resultType ) else Seq( argType ) ) )
    }
    val recursorType = FunctionType( resultType, recTypes :+ indType )
    Const( indType.name + "Rec", recursorType, indType.params :+ resultType )
  }

  /**
   * Transforms a context into system T.
   *
   * @param ctx original context
   * @return original context with recursors for inductive types, pair and sum types and terms, and the empty program
   */
  def systemT( ctx: Context ): Context = {
    implicit var systemT = ctx

    // add recursors for all inductive types
    for ( ( name, constructors ) <- systemT.get[StructurallyInductiveTypes].constructors.filter( _._1 != "o" ) ) {
      val indType = systemT.get[BaseTypes].baseTypes( name )

      val resultTypeVariable = TVar( new NameGenerator( typeVariables( indType ) map ( _.name ) ).fresh( "a" ) )
      val rec @ Const( _, FunctionType( _, recCaseTypes :+ _ ), _ ) = recursor( indType, resultTypeVariable )( ctx )

      val ngTermVariableNames = new NameGenerator( systemT.constants map ( _.name ) )

      val constrArgVars = constructors.map {
        case constr @ Const( _, FunctionType( _, argTypes ), _ ) =>
          constr -> argTypes.map( argType => Var( ngTermVariableNames.fresh( "x" ), argType ) )
      } toMap

      val recCaseVars = recCaseTypes.map( recCaseType => Var( ngTermVariableNames.fresh( "x" ), recCaseType ) )
      val constr_recCaseVars = constructors.zip( recCaseVars ) toMap

      val equations = constructors.map( constr => (
        rec( recCaseVars :+ constr( constrArgVars( constr ) ) ),
        constr_recCaseVars( constr )( constrArgVars( constr ).flatMap( argVar =>
          if ( argVar.ty == indType ) Seq( argVar, rec( recCaseVars :+ argVar ) ) else Seq( argVar ) ) ) ) )

      systemT += PrimRecFun( rec, equations )
    }

    // add conjuctive type, pairs, projections and their reduction rules
    val a = TVar( "a" )
    val b = TVar( "b" )
    val conj = ty"conj ?a ?b"
    val pair = hoc"pair{?a ?b}: ?a > ?b > (conj ?a ?b)"
    systemT += InductiveType( conj, pair )
    val pi1 = hoc"pi1{?a ?b}: (conj ?a ?b) > ?a"
    val pi2 = hoc"pi2{?a ?b}: (conj ?a ?b) > ?b"
    val x: Expr = hov"x : ?a"
    val y: Expr = hov"y : ?b"
    systemT += PrimRecFun(
      pi1, List(
      ( pi1( pair( x, y ) ) -> x ) ) )( systemT )
    systemT += PrimRecFun(
      pi2, List(
      ( pi2( pair( x, y ) ) -> y ) ) )( systemT )

    // add sum type
    val sum = ty"sum ?a ?b"
    val inl = hoc"inl{?a ?b}: ?a > (sum ?a ?b)"
    val inr = hoc"inr{?a ?b}: ?b > (sum ?a ?b)"
    systemT += InductiveType( sum, inl, inr )
    val matchSum = hoc"matchSum{?a ?b ?c}: (sum ?a ?b) > (?a > ?c) > (?b > ?c) > ?c"
    val w1: Expr = hov"w1: ?a > ?c"
    val w2: Expr = hov"w2: ?b > ?c"
    systemT += PrimRecFun(
      matchSum, List(
      ( matchSum( inl( x ), w1, w2 ) -> w1( x ) ),
      ( matchSum( inr( y ), w1, w2 ) -> w2( y ) ) ) )( systemT )

    // add a term+type to represent the empty program
    systemT += InductiveType(
      ty"1",
      hoc"i : 1" )

    systemT
  }

  /**
   * Extracts an mrealizer for a theorem from its proof.
   *
   * @param proof proof from which the realizer is extracted
   * @param re boolean whether or not the result should be normalized with respect to the empty program (default) or not
   * @param ctx system T
   * @return a term M of system T, and
   *         a map of sequentindices of the antecedent of the conclusion of the proof, to variables x1,...,xk, such that:
   *         if M1,...,Mk are m-realizers for the formulas in the antecedent,
   *         then M[M1/x1]...[Mk/xk] m-realizes the succedent of the conclusion
   */
  def mrealize( proof: NDProof, re: Boolean = true )( implicit ctx: Context ): ( Map[SequentIndex, Var], Expr ) = {

    val context = systemT( ctx )

    val ng = new NameGenerator( freeVariablesND( proof ).map( _.name ) )
    val varsAnt = proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( ng.fresh( "y" ), flat( x._1 ) ) ) ).toMap

    val mrealizer = mrealizeCases( proof, varsAnt, ng )( context )

    if ( re )
      ( varsAnt map ( x => ( x._1, Var( x._2.name, remEmpProgType( x._2.ty )( context ) ) ) ),
        remEmpProg( mrealizer )( context ) )
    else ( varsAnt, mrealizer )
  }

  private def mrealizeCases( proof: NDProof, variables: Map[SequentIndex, Var], ng: NameGenerator )( implicit systemT: Context ): Expr = {

    proof match {
      case WeakeningRule( subProof, formula ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )

      case ContractionRule( subProof, aux1, aux2 ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )

      case LogicalAxiom( formula ) =>
        variables.head._2

      case AndElim1Rule( subProof ) =>
        le"pi1(${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )})"

      case AndElim2Rule( subProof ) =>
        le"pi2(${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )})"

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        le"pair(${
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng )
        },${
          mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )
        })"

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        val varA = Var( ng.fresh( "y" ), flat( middleSubProof.conclusion( aux1 ) ) )
        val varB = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux2 ) ) )
        le"matchSum( ${
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng )
        },${
          Abs( varA, mrealizeCases( middleSubProof, varsAntPrem( proof, variables, 1 ) + ( aux1 -> varA ), ng ) )
        },${
          Abs( varB, mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 2 ) + ( aux2 -> varB ), ng ) )
        })"

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        val leftType = flat( subProof.endSequent( Suc( 0 ) ) )
        val rightType = flat( rightDisjunct )
        val inl = systemT.constant( "inl", List( leftType, rightType ) ).get
        inl( mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        val leftType = flat( leftDisjunct )
        val rightType = flat( subProof.endSequent( Suc( 0 ) ) )
        val inr = systemT.constant( "inr", List( leftType, rightType ) ).get
        inr( mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        App(
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng ),
          mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng ) )

      case ImpIntroRule( subProof, aux ) =>
        val extraVar = Var( ng.fresh( "y" ), flat( subProof.conclusion( aux ) ) )
        Abs( extraVar, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ), ng ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        App(
          mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng ),
          mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng ) )

      case NegIntroRule( subProof, aux ) =>
        val extraVar = Var( ng.fresh( "y" ), flat( subProof.conclusion( aux ) ) )
        Abs( extraVar, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ), ng ) )

      case TopIntroRule =>
        val varr = Var( ng.fresh( "y" ), ty"1" )
        Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        Var( ng.fresh( "y" ), flat( mainFormula ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs( eigenVariable, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ) )

      case ForallElimRule( subProof, term ) =>
        App( mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ), term )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        le"pair($term,${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )})"

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val mrealizerLeft = mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng )
        val extraVar = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux ) ) )
        val sub = Substitution(
          eigenVariable -> le"pi1($mrealizerLeft)",
          extraVar -> le"pi2($mrealizerLeft)" )
        sub( mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) + ( aux -> extraVar ), ng ) )

      case TheoryAxiom( mainFormula ) =>
        Var( ng.fresh( s"mrealizer($mainFormula)" ), flat( mainFormula ) )

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )

      case EqualityIntroRule( term ) =>
        le"i"

      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val indType @ TBase( name, params ) = term.ty
        val resultType = flat( proof.conclusion( Suc( 0 ) ) )
        def mrealizerConstrCase( cas: InductionCase, index: Int ): Expr = {
          val eigenvarsIndTy = cas.eigenVars.filter( _.ty == indType ).zip( cas.hypotheses.map( _ -> Var( ng.fresh( "y" ), resultType ) ) ) toMap
          val mrealizerCase = mrealizeCases( cas.proof, varsAntPrem( proof, variables, index ) ++ eigenvarsIndTy.values, ng )
          val abstractedVrs = cas.eigenVars.flatMap( eigenVar => if ( eigenVar.ty == indType ) Seq( eigenVar, eigenvarsIndTy( eigenVar )._2 ) else Seq( eigenVar ) )
          Abs( abstractedVrs, mrealizerCase )
        }
        val rec = recursor( indType, resultType )
        rec( cases.zipWithIndex.map( caseInd => mrealizerConstrCase( caseInd._1, caseInd._2 ) ) :+ term )

      // Assumes that the definition rule is applied according to rewrite rules of the original context.
      case DefinitionRule( subProof, mainFormula ) =>
        mrealizeCases( subProof, variables, ng )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        val A = leftSubProof.conclusion( aux1 )
        val notA = rightSubProof.conclusion( aux2 )
        val AorNotA = Or( A, notA )
        val varA = Var( ng.fresh( "y" ), flat( A ) )
        val varNotA = Var( ng.fresh( "y" ), flat( notA ) )
        le"matchSum( ${Var( ng.fresh( s"mrealizer($AorNotA)" ), flat( AorNotA ) )},${
          Abs( varA, mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) + ( aux1 -> varA ), ng ) )
        },${
          Abs( varNotA, mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) + ( aux2 -> varNotA ), ng ) )
        })"
    }
  }

  /**
   * computes the type of a potential m-realizer for the formula
   */
  def flat( formula: Formula )( implicit systemT: Context ): Ty = formula match {
    case Bottom()                         => ty"1"
    case Top()                            => flat( Imp( Bottom(), Bottom() ) )
    case Eq( _, _ )                       => ty"1"
    case Atom( _, _ )                     => ty"1" // ?
    case And( leftformula, rightformula ) => TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( leftformula, rightformula )  => TBase( "sum", flat( leftformula ), flat( rightformula ) )
    case Imp( leftformula, rightformula ) => flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula )                => flat( Imp( subformula, Bottom() ) )
    case Ex( variable, subformula )       => TBase( "conj", variable.ty, flat( subformula ) )
    case All( variable, subformula )      => variable.ty ->: flat( subformula )
  }

  /**
   * removes all occurences of the empty program i : 1 from term, or is i : 1 itself,
   * except for match and inl and inr term: sometimes not possible to remove all occurences.
   */
  def remEmpProg( term: Expr )( implicit systemT: Context ): Expr = {

    val empty = hoc"i"
    val emptyType = ty"1"

    term match {

      case Var( name, typee ) =>
        val typeeR = remEmpProgType( typee )
        if ( typeeR == emptyType ) empty
        else Var( name, typeeR )

      // if term is only a constant, it is a recursor (other constants are catched by applications to them)
      case Const( recName, FunctionType( resultType, recTypes :+ indType ), params ) =>
        val resultTypeR = remEmpProgType( resultType )
        if ( resultTypeR == emptyType ) empty
        else Const( recName, FunctionType( resultTypeR, remEmpProgTypes( recTypes ) :+ indType ), remEmpProgTypes( params ) )

      case Abs( variable, termm ) =>
        val termmR = remEmpProg( termm )
        if ( termmR == empty ) empty
        else if ( remEmpProgType( variable.ty ) == emptyType ) termmR
        else Abs( Var( variable.name, remEmpProgType( variable.ty ) ), termmR )

      case App( App( Const( "pair", conjtype, params ), left ), right ) =>
        val leftR = remEmpProg( left )
        val rightR = remEmpProg( right )
        if ( rightR == empty ) leftR
        else if ( leftR == empty ) rightR
        else Const( "pair", remEmpProgType( conjtype ), remEmpProgTypes( params ) )( leftR, rightR )

      case App( Const( "pi1", TArr( TBase( "conj", typeparams ), termmtype ), params ), termm ) =>
        if ( remEmpProgType( typeparams( 0 ) ) == emptyType ) empty
        else if ( remEmpProgType( typeparams( 1 ) ) == emptyType ) remEmpProg( termm )
        else Const(
          "pi1",
          TArr( TBase( "conj", remEmpProgTypes( typeparams ) ), remEmpProgType( termmtype ) ),
          remEmpProgTypes( params ) )( remEmpProg( termm ) )

      case App( Const( "pi2", TArr( TBase( "conj", typeparams ), termmtype ), params ), termm ) =>
        if ( remEmpProgType( typeparams( 1 ) ) == emptyType ) empty
        else if ( remEmpProgType( typeparams( 0 ) ) == emptyType ) remEmpProg( termm )
        else Const(
          "pi2",
          TArr( TBase( "conj", remEmpProgTypes( typeparams ) ), remEmpProgType( termmtype ) ),
          remEmpProgTypes( params ) )( remEmpProg( termm ) )

      case App( Const( "inl", TArr( termmtype, TBase( "sum", typeparams ) ), params ), termm ) =>
        Const(
          "inl",
          TArr( remEmpProgType( termmtype ), TBase( "sum", remEmpProgTypes( typeparams ) ) ),
          remEmpProgTypes( params ) )( remEmpProg( termm ) )

      case App( Const( "inr", TArr( termmtype, TBase( "sum", typeparams ) ), params ), termm ) =>
        Const(
          "inr",
          TArr( remEmpProgType( termmtype ), TBase( "sum", remEmpProgTypes( typeparams ) ) ),
          remEmpProgTypes( params ) )( remEmpProg( termm ) )

      case App( App( App( Const( "matchSum", TArr( TBase( "sum", sumparams ), TArr( leftType, TArr( rightType, resultType ) ) ), params ), in ), left ), right ) =>
        val leftR = remEmpProg( left )
        val rightR = remEmpProg( right )
        val ng = new NameGenerator( ( freeVariables( left ) ++ freeVariables( right ) ) map ( _.name ) )
        val leftRN = if ( remEmpProgType( sumparams( 0 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), leftR ) else leftR
        val rightRN = if ( remEmpProgType( sumparams( 1 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), rightR ) else rightR
        val resultTypeR = remEmpProgType( resultType )
        if ( resultTypeR == emptyType ) empty
        else Const(
          "matchSum",
          TArr( remEmpProgType( TBase( "sum", sumparams ) ), TArr( leftRN.ty, TArr( rightRN.ty, resultTypeR ) ) ),
          remEmpProgTypes( params ) )( remEmpProg( in ), leftRN, rightRN )

      case App( term1, term2 ) =>
        val term1R = remEmpProg( term1 )
        val term2R = remEmpProg( term2 )
        if ( term1R == empty ) empty
        else if ( term2R == empty ) term1R
        else App( term1R, term2R )

      case _ => term
    }
  }

  /**
   * removes all occurences of the empty program type 1 from term, or is 1 itself,
   * except for the sum type.
   */
  def remEmpProgType( typee: Ty )( implicit systemT: Context ): Ty = {

    val empty = ty"1"

    typee match {

      case TBase( "conj", params ) =>
        val leftconj = remEmpProgType( params( 0 ) )
        val rightconj = remEmpProgType( params( 1 ) )
        if ( leftconj == empty ) rightconj
        else if ( rightconj == empty ) leftconj
        else TBase( "conj", leftconj, rightconj )

      case TBase( "sum", params ) =>
        val leftsum = remEmpProgType( params( 0 ) )
        val rightsum = remEmpProgType( params( 1 ) )
        TBase( "sum", leftsum, rightsum )

      case TArr( in, out ) =>
        val inR = remEmpProgType( in )
        val outR = remEmpProgType( out )
        if ( outR == empty ) empty
        else if ( inR == empty ) outR
        else TArr( inR, outR )

      case _ => typee
    }
  }

  def remEmpProgTypes( types: List[Ty] )( implicit systemT: Context ): List[Ty] =
    types.map( remEmpProgType( _ ) )

  // Given a proof and variables for the formulas in the antecedent of the conlusion,
  // returns those variables that occur as well in the antecedent of the conclusion of the premise at premisenumber.
  private def varsAntPrem( proof: NDProof, varsAntConcl: Map[SequentIndex, Var], premiseNumber: Int ): Map[SequentIndex, Var] = {
    varsAntConcl.flatMap {
      case ( index, variable ) =>
        proof.occConnectors( premiseNumber ).parents( index ).map( pindex => pindex -> variable )
    }
  }

}