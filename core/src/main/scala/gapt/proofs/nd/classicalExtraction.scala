package gapt.proofs.nd

import gapt.expr.{ App, Substitution, Ty, typeVariables, _ }
import gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import gapt.proofs._
import gapt.utils.NameGenerator

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
    val conj = ty"conj ?a ?b"
    val pair = hoc"pair{?a ?b}: ?a > ?b > (conj ?a ?b)"
    systemT += InductiveType( conj, pair )
    val pi1 = hoc"pi1{?a ?b}: (conj ?a ?b) > ?a"
    val pi2 = hoc"pi2{?a ?b}: (conj ?a ?b) > ?b"
    val x: Expr = hov"x : ?a"
    val y: Expr = hov"y : ?b"
    systemT += PrimRecFun( List(
      ( pi1, List(
        ( pi1( pair( x, y ) ) -> x ) ) ) ) )( systemT )
    systemT += PrimRecFun( List(
      ( pi2, List(
        ( pi2( pair( x, y ) ) -> y ) ) ) ) )( systemT )

    // add sum type
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

    //val bar = hoc"bar{?a}: ?a > ?a > hyp > ?a"
    //val hyp = ty"hyp"
    //systemT += InductiveType( hyp, bar )

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

    //val handle = hoc"handle{?a ?b}: (?a > ?b) > ((?a > (exn ?a)) > ?b) > ?b"
    val bar = hoc"bar{?b}: ?b > ?b > ?b"
    systemT += bar

    val bar2 = hoc"bar2{?a ?b ?c}: (?a > ?c) > (?b > ?c) > ?c"
    systemT += bar2

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

    // should actually be free variables of whole proof - need to implement this
    val ng = new NameGenerator( freeVariables( proof.conclusion ).map( _.name ) )
    val varsAnt = proof.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( ng.fresh( "y" ), flat( x._1 ) ) ) ).toMap

    val mrealizer = mrealizeCases( proof, varsAnt, ng )( context )

    // by default: remove occurences of the empty program
    if ( re )
      ( varsAnt map ( x => ( x._1, Var( x._2.name, remEmpProgType( x._2.ty )( context ) ) ) ),
        remEmpProg( mrealizer )( context ) )
    else ( varsAnt, mrealizer )
  }

  def mrealizeCases( proof: NDProof, variables: Map[SequentIndex, Var], ng: NameGenerator )( implicit systemT: Context ): Expr = {

    proof match {
      case WeakeningRule( subProof, formula ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )

      case ContractionRule( subProof, aux1, aux2 ) =>
        mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )

      case LogicalAxiom( All( x, f ) ) =>
        println( "Axiom case All" )
        variables.head._2

      case LogicalAxiom( Ex( x, Neg( f ) ) ) =>
        println( "Axiom case Ex" )
        variables.head._2

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

      // TODO: I think NegIntroRule should produce a term of type ?a > (exn ?a)
      case NegIntroRule( subProof, aux ) =>
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        val subProofRealizer = mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ), ng )
        val exception = systemT.constant( "exception", List( extraVar.ty ) ).get
        //val tmp = App( subProofRealizer, insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) )
        // TODO
        val tmp = exception( extraVar )
        //Abs( variablesAntConclusion( proof ) :+ extraVar, App( subProofRealizer, variablesAntConclusion( proof ) ) )
        Abs( extraVar, tmp )

      case TopIntroRule() =>
        val varr = Var( "z", ty"1" )
        Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        val subProofRealizer = mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )
        // TODO is this true in general?
        val exnTypeParameter = subProofRealizer.ty match {
          case TBase( "exn", param :: Nil ) => param
          case _                            => throw new Exception( "Realizer must be of type exn ?a." )
        }

        /*
        val tmp = subProofRealizer match {
          case Abs.Block( _, e ) =>
            e.ty match {
              case TBase( "exn", param :: Nil ) => param
              case _                            => throw new Exception( "Realizer must be of type exn ?a." )
            }
        }
        */

        val raisedType = flat( mainFormula )
        val raise = systemT.constant( "raise", List( exnTypeParameter, raisedType ) ).get
        // TODO reverse makes App in ExcludedMiddle realizer work (example6)
        // TODO reverse makes App in ExcludedMiddle realizer fail (example7)
        //Abs( variablesAntConclusion( proof ).reverse, raise( App( subProofRealizer, variablesAntPremise( proof, 0 ) ) ) )
        raise( subProofRealizer )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        Abs( eigenVariable, mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ) )

      case ForallElimRule( subProof, term ) =>
        App( mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng ), term )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        le"pair($term,${mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ), ng )})"

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val mrealizerLeft = mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ), ng )
        val sub1 = Substitution( eigenVariable, le"pi1($mrealizerLeft)" )
        val extraVar = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux ) ) )
        val sub2 = Substitution( extraVar, le"pi2($mrealizerLeft)" )
        sub1( sub2( mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) + ( aux -> extraVar ), ng ) ) )

      // only to be used when mainFormula is an equation
      case TheoryAxiom( mainFormula ) =>
        le"i"

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )

      case EqualityIntroRule( term ) =>
        le"i"

      // Works only for the type of natural numbers at the moment
      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val extraVar = Var( ng.fresh( "y" ), flat( proof.conclusion( Suc( 0 ) ) ) )
        val mrealizerBaseCase = mrealizeCases( cases( 0 ).proof, varsAntPrem( proof, variables, 0 ), ng )
        val mrealizerInductionCase = Abs(
          cases( 1 ).eigenVars :+ extraVar,
          mrealizeCases( cases( 1 ).proof, varsAntPrem( proof, variables, 1 ) + ( cases( 1 ).hypotheses( 0 ) -> extraVar ), ng ) )
        le"natRec($mrealizerBaseCase,$mrealizerInductionCase,$term)"

      // assuming that the definitionrule is applied according to rewrite rules of the original context
      case DefinitionRule( subProof, mainFormula ) =>
        mrealizeCases( subProof, variables, ng )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        leftSubProof.endSequent( aux1 ) match {
          case f @ Ex( x, g ) =>
            val left = nd.ProofBuilder.
              c( nd.LogicalAxiom( Ex( x, -( -g ) ) ) ).
              c( nd.LogicalAxiom( g ) ).
              c( nd.LogicalAxiom( -( -( g ) ) ) ).
              c( nd.LogicalAxiom( -g ) ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, g ) ).
              b( ExcludedMiddleRule( _, Ant( 0 ), _, ( Ant( 1 ) ) ) ).
              u( ExistsIntroRule( _, f ) ).
              b( ExistsElimRule( _, _ ) ).
              qed
            //println( "mrealize left" )
            //println( mrealizeCases( left, Map.empty, ng ) )
            // TODO:
            //val varsAnt = left.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( ng.fresh( "hyp" ), flat( x._1 ) ) ) ).toMap
            //println( mrealizeCases( left, varsAnt, ng ) )

            val tl = nd.ProofBuilder.
              c( leftSubProof ).
              u( ImpIntroRule( _, aux1 ) ).
              c( left ).
              b( ImpElimRule( _, _ ) ).
              qed
            println( "left" )
            println( left )
            println( "tl" )
            println( tl )
            println( "mrealize tl" )
            //val l = mrealizeCases( tl, varsAnt, ng )
            val varA = Var( ng.fresh( "hyp" ), flat( tl.conclusion( Ant( 0 ) ) ) )
            val l = mrealizeCases( tl, varsAntPrem( proof, variables, 0 ) + ( Ant( 0 ) -> varA ), ng )
            println( l )

            val right = nd.ProofBuilder.
              c( nd.LogicalAxiom( Ex( x, g ) ) ).
              c( nd.LogicalAxiom( -g ) ).
              c( nd.LogicalAxiom( g ) ).
              b( NegElimRule( _, _ ) ).
              u( ImpIntroRule( _, -g ) ).
              c( nd.LogicalAxiom( All( x, -g ) ) ).
              u( ForallElimRule( _, x ) ).
              b( ImpElimRule( _, _ ) ).
              b( ExistsElimRule( _, _ ) ).
              u( NegIntroRule( _, f ) ).
              qed
            //println( "mrealize right" )
            // TODO:
            //val varsAnt2 = right.conclusion.zipWithIndex.antecedent.map( x => ( x._2, Var( ng.fresh( "hyp" ), flat( x._1 ) ) ) ).toMap
            //println( mrealizeCases( right, varsAnt2, ng ) )
            val tr = nd.ProofBuilder.
              c( rightSubProof ).
              u( ImpIntroRule( _, aux2 ) ).
              c( right ).
              b( ImpElimRule( _, _ ) ).
              qed
            println( "right" )
            println( right )
            println( "tr" )
            println( tr )
            println( "mrealize tr" )
            val varB = Var( ng.fresh( "hyp" ), flat( tr.conclusion( Ant( 0 ) ) ) )
            val r = mrealizeCases( tr, varsAntPrem( proof, variables, 1 ) + ( Ant( 0 ) -> varB ), ng )
            println( r )

            println( "l.ty " + l.ty )
            println( "r.ty " + r.ty )
            le"bar2 ${Abs( varA, l )} ${Abs( varB, r )}"
          case _ =>
            val varA = Var( ng.fresh( "hyp" ), flat( leftSubProof.conclusion( aux1 ) ) )
            //val left = Abs( varA, mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) + ( aux1 -> varA ), ng ) )
            val left = mrealizeCases( leftSubProof, varsAntPrem( proof, variables, 0 ) + ( aux1 -> varA ), ng )
            val varB = Var( ng.fresh( "hyp" ), flat( rightSubProof.conclusion( aux2 ) ) )
            //val right = Abs( varB, mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) + ( aux2 -> varB ), ng ) )
            val right = mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ) + ( aux2 -> varB ), ng )
            le"bar $left $right"
        }

    }
  }
  def extractCases( proof: NDProof )( implicit ctx: Context ): Expr = {
    val ng = new NameGenerator( freeVariables( proof.conclusion ).map( _.name ) )
    extractCases( proof, ng )( systemT( ctx ) )( Suc( 0 ) )
  }

  def extractCases( proof: NDProof, ng: NameGenerator )( implicit systemT: Context ): Sequent[Expr] = {

    proof match {
      case WeakeningRule( subProof, formula ) =>
        extractCases( subProof, ng )

      case ContractionRule( subProof, aux1, aux2 ) =>
        extractCases( subProof, ng )

      case LogicalAxiom( formula @ All( x, f ) ) =>
        println( "Axiom case All" )
        // TODO:
        val v = Var( ng.fresh( "y" ), flat( formula ) )
        v +: Sequent() :+ v

      case LogicalAxiom( formula @ Ex( x, Neg( f ) ) ) =>
        println( "Axiom case Ex" )
        // TODO:
        val v = Var( ng.fresh( "y" ), flat( formula ) )
        v +: Sequent() :+ v

      case LogicalAxiom( formula ) =>
        val v = Var( ng.fresh( "y" ), flat( formula ) )
        v +: Sequent() :+ v

      case AndElim1Rule( subProof ) =>
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), le"pi1(${s( Suc( 0 ) )})" )

      case AndElim2Rule( subProof ) =>
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), le"pi2(${s( Suc( 0 ) )})" )

      case AndIntroRule( leftSubProof, rightSubProof ) =>
        val l = extractCases( leftSubProof, ng )
        val r = extractCases( rightSubProof, ng )
        // TODO: order
        l.antecedent ++: r.antecedent ++: Sequent() :+ le"pair(${l( Suc( 0 ) )},${r( Suc( 0 ) )})"

      case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
        val l = extractCases( leftSubProof, ng )
        val m = extractCases( middleSubProof, ng )
        val r = extractCases( rightSubProof, ng )
        val varA = m( aux1 ).asInstanceOf[Var]
        val varB = r( aux2 ).asInstanceOf[Var]
        // TODO: order
        l.antecedent ++: m.antecedent ++: r.antecedent ++: Sequent() :+
          le"matchSum( ${
            l( Suc( 0 ) )
          },${
            Abs( varA, m( Suc( 0 ) ) )
          },${
            Abs( varB, r( Suc( 0 ) ) )
          })"

      case OrIntro1Rule( subProof, rightDisjunct ) =>
        val leftType = flat( subProof.endSequent( Suc( 0 ) ) )
        val rightType = flat( rightDisjunct )
        val inl = systemT.constant( "inl", List( leftType, rightType ) ).get
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), inl( s( Suc( 0 ) ) ) )

      case OrIntro2Rule( subProof, leftDisjunct ) =>
        val leftType = flat( leftDisjunct )
        val rightType = flat( subProof.endSequent( Suc( 0 ) ) )
        val inr = systemT.constant( "inr", List( leftType, rightType ) ).get
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), inr( s( Suc( 0 ) ) ) )

      case ImpElimRule( leftSubProof, rightSubProof ) =>
        val l = extractCases( leftSubProof, ng )
        val r = extractCases( rightSubProof, ng )
        l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )

      case ImpIntroRule( subProof, aux ) =>
        val s = extractCases( subProof, ng )
        val extraVar = s( aux ).asInstanceOf[Var]
        s.replaceAt( Suc( 0 ), Abs( extraVar, s( Suc( 0 ) ) ) )

      case NegElimRule( leftSubProof, rightSubProof ) =>
        val l = extractCases( leftSubProof, ng )
        val r = extractCases( rightSubProof, ng )
        l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )

      // TODO: I think NegIntroRule should produce a term of type ?a > (exn ?a)
      case NegIntroRule( subProof, aux ) =>
        val s = extractCases( subProof, ng )
        val extraVar = s( aux ).asInstanceOf[Var]
        s.replaceAt( Suc( 0 ), Abs( extraVar, s( Suc( 0 ) ) ) )
      /*
        val extraVar = Var( "z", flat( subProof.conclusion( aux ) ) )
        val subProofRealizer = mrealizeCases( subProof, varsAntPrem( proof, variables, 0 ) + ( aux -> extraVar ), ng )
        val exception = systemT.constant( "exception", List( extraVar.ty ) ).get
        //val tmp = App( subProofRealizer, insertIndex( variablesAntPremise( proof, 0 ), aux, extraVar ) )
        // TODO
        val tmp = exception( extraVar )
        //Abs( variablesAntConclusion( proof ) :+ extraVar, App( subProofRealizer, variablesAntConclusion( proof ) ) )
        Abs( extraVar, tmp )
        */

      case TopIntroRule() =>
        ???
      //val varr = Var( "z", ty"1" )
      //Abs( varr, varr )

      case BottomElimRule( subProof, mainFormula ) =>
        val s = extractCases( subProof, ng )
        // TODO is this true in general?
        val exnTypeParameter = s( Suc( 0 ) ).ty match {
          case TBase( "exn", param :: Nil ) => param
          case _                            => throw new Exception( "Realizer must be of type exn ?a." )
        }

        /*
        val tmp = subProofRealizer match {
          case Abs.Block( _, e ) =>
            e.ty match {
              case TBase( "exn", param :: Nil ) => param
              case _                            => throw new Exception( "Realizer must be of type exn ?a." )
            }
        }
        */

        val raisedType = flat( mainFormula )
        val raise = systemT.constant( "raise", List( exnTypeParameter, raisedType ) ).get
        // TODO reverse makes App in ExcludedMiddle realizer work (example6)
        // TODO reverse makes App in ExcludedMiddle realizer fail (example7)
        //Abs( variablesAntConclusion( proof ).reverse, raise( App( subProofRealizer, variablesAntPremise( proof, 0 ) ) ) )
        s.replaceAt( Suc( 0 ), raise( s( Suc( 0 ) ) ) )

      case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), Abs( eigenVariable, s( Suc( 0 ) ) ) )

      case ForallElimRule( subProof, term ) =>
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), App( s( Suc( 0 ) ), term ) )

      case ExistsIntroRule( subProof, formula, term, variable ) =>
        val s = extractCases( subProof, ng )
        s.replaceAt( Suc( 0 ), le"pair($term,${s( Suc( 0 ) )})" )

      case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
        val l = extractCases( leftSubProof, ng )
        val r = extractCases( rightSubProof, ng )

        val sub1 = Substitution( eigenVariable, le"pi1(${l( Suc( 0 ) )})" )
        val extraVar = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux ) ) )
        val sub2 = Substitution( extraVar, le"pi2(${l( Suc( 0 ) )})" )
        l.antecedent ++: r.antecedent ++: Sequent() :+ sub1( sub2( r( Suc( 0 ) ) ) )

      // only to be used when mainFormula is an equation
      case TheoryAxiom( mainFormula ) =>
        ???
      //le"i"

      case EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
        ???
      //mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )

      case EqualityIntroRule( term ) =>
        ???
      //le"i"

      // Works only for the type of natural numbers at the moment
      // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
      case InductionRule( cases, formula, term ) =>
        val baseCase = extractCases( cases( 0 ).proof, ng )
        val inductionCase = extractCases( cases( 1 ).proof, ng )
        baseCase.antecedent ++: inductionCase.antecedent ++: Sequent() :+
          le"natRec(${baseCase( Suc( 0 ) )},${inductionCase( Suc( 0 ) )},$term)"

      // assuming that the definitionrule is applied according to rewrite rules of the original context
      case DefinitionRule( subProof, mainFormula ) =>
        extractCases( subProof, ng )

      case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        leftSubProof.endSequent( aux1 ) match {
          case f @ Ex( x, g ) =>
            val left = nd.ProofBuilder.
              c( nd.LogicalAxiom( Ex( x, -( -g ) ) ) ).
              c( nd.LogicalAxiom( g ) ).
              c( nd.LogicalAxiom( -( -( g ) ) ) ).
              c( nd.LogicalAxiom( -g ) ).
              b( NegElimRule( _, _ ) ).
              u( BottomElimRule( _, g ) ).
              b( ExcludedMiddleRule( _, Ant( 0 ), _, ( Ant( 1 ) ) ) ).
              u( ExistsIntroRule( _, f ) ).
              b( ExistsElimRule( _, _ ) ).
              qed
            println( "extractCases left" )
            //println( mrealizeCases( left, Map.empty, ng ) )
            println( extractCases( left, ng ) )

            val tl = nd.ProofBuilder.
              c( leftSubProof ).
              u( ImpIntroRule( _, aux1 ) ).
              c( left ).
              b( ImpElimRule( _, _ ) ).
              qed
            println( "left" )
            println( left )
            println( "tl" )
            println( tl )

            val right = nd.ProofBuilder.
              c( nd.LogicalAxiom( Ex( x, g ) ) ).
              c( nd.LogicalAxiom( -g ) ).
              c( nd.LogicalAxiom( g ) ).
              b( NegElimRule( _, _ ) ).
              u( ImpIntroRule( _, -g ) ).
              c( nd.LogicalAxiom( All( x, -g ) ) ).
              u( ForallElimRule( _, x ) ).
              b( ImpElimRule( _, _ ) ).
              b( ExistsElimRule( _, _ ) ).
              u( NegIntroRule( _, f ) ).
              qed
            println( "extractCases right" )
            println( extractCases( right, ng ) )
            val tr = nd.ProofBuilder.
              c( rightSubProof ).
              u( ImpIntroRule( _, aux2 ) ).
              c( right ).
              b( ImpElimRule( _, _ ) ).
              qed
            println( "right" )
            println( right )
            println( "tr" )
            println( tr )

            ???
          case _ =>
            val l = extractCases( leftSubProof, ng )
            val r = extractCases( rightSubProof, ng )
            l.antecedent ++: r.antecedent ++: Sequent() :+ le"bar ${l( Suc( 0 ) )} ${r( Suc( 0 ) )}"
        }

    }
  }

  // computes the type of a potential m-realizer for the formula
  def flat( formula: Formula )( implicit systemT: Context ): Ty = formula match {
    case Bottom()                         => ty"1"
    case Top()                            => flat( Imp( Bottom(), Bottom() ) )
    case Eq( _, _ )                       => ty"1"
    case Atom( _, _ )                     => ty"1" // ?
    case And( leftformula, rightformula ) => TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( leftformula, rightformula )  => TBase( "sum", flat( leftformula ), flat( rightformula ) )
    case Imp( leftformula, rightformula ) => flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula )                => flat( subformula ) ->: TBase( "exn", flat( subformula ) ) //flat( Imp( subformula, Bottom() ) )
    case Ex( variable, subformula )       => TBase( "conj", variable.ty, flat( subformula ) )
    case All( variable, subformula )      => variable.ty ->: flat( subformula )
  }

  // removes all occurences of the empty program i : 1 from term, or is i : 1 itself,
  // except for match and inl and inr term: sometimes not possible to remove all occurences.
  // works only for recursors for natural numbers now
  def remEmpProg( term: Expr )( implicit systemT: Context ): Expr = {

    val empty = hoc"i"
    val emptyType = ty"1"

    term match {

      case Var( name, typee ) =>
        val typeeR = remEmpProgType( typee )
        if ( typeeR == emptyType ) empty
        else Var( name, typeeR )

      case Const( "natRec", _, params ) =>
        val parameter = remEmpProgType( params.head )
        if ( parameter == emptyType ) empty
        else Const( "natRec", parameter ->: ( ty"nat" ->: parameter ->: parameter ) ->: ty"nat" ->: parameter, List( parameter ) )

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

  // similar but for types
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
  def varsAntPrem( proof: NDProof, varsAntConcl: Map[SequentIndex, Var], premiseNumber: Int ): Map[SequentIndex, Var] = {
    val positions: Vector[( Seq[SequentIndex], SequentIndex )] = proof.occConnectors( premiseNumber ).childrenSequent.zipWithIndex.antecedent
    val variables: Vector[( Seq[Option[Var]], SequentIndex )] = positions.map( x => ( x._1.map( y => varsAntConcl.get( y ) ), x._2 ) )
    val flattened: Vector[( Seq[Var], SequentIndex )] = variables.map( x => ( x._1.flatten, x._2 ) )
    flattened.flatMap( x => x._1.map( y => ( x._2, y ) ) ).toMap
  }

}

class ClassicalExtractionCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

