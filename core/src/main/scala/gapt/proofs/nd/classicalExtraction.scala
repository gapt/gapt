package gapt.proofs.nd

import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.expr.{ App, Substitution, Ty, typeVariables, _ }
import gapt.proofs.Context.{ BaseTypes, InductiveType, PrimRecFun, StructurallyInductiveTypes }
import gapt.proofs._
import gapt.utils.NameGenerator

import scala.collection.mutable

object ClassicalExtraction {

  private val varMap: mutable.Map[Formula, Var] = mutable.Map.empty
  private def getVar( name: String, f: Formula, nameGenerator: NameGenerator )( implicit ctx: Context ) = {
    if ( varMap.contains( f ) ) {
      varMap( f )
    } else {
      val v = Var( nameGenerator.fresh( name ), flat( f ) )
      varMap += ( f -> v )
      v
    }
  }

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

    /*
    val exn = ty"exn ?a"
    val exception = hoc"exception{?a}: ?a > (exn ?a)"
    systemT += InductiveType( exn, exception )
    val raise = hoc"raise{?a ?b}: (exn ?a) > ?b"
    systemT += raise
    */
    systemT += TBase( "exn" )
    val exception = hoc"exception{?a}: ?a > exn"
    //systemT += InductiveType( exn, exception )
    systemT += exception
    val efq = hoc"efq{?b}: exn > ?b"
    systemT += efq
    /*
    val e: Expr = Var( "e", exn )
    systemT += PrimRecFun( List(
      ( raise, List(
        //( raise( e )( y ) -> raise( e ) ) ) ) ) )( systemT )
        ( raise( raise( e ) ) -> raise( e ) ) ) ) ) )( systemT )
    */

    //val handle = hoc"handle{?a ?b}: (?a > ?b) > ((?a > (exn ?a)) > ?b) > ?b"
    val bar = hoc"bar{?a ?b ?c}: (?a > ?c) > (?b > ?c) > ?c"
    systemT += bar

    val bar2 = hoc"bar2{?x ?a ?b ?c}: (?x > o) > (?a > ?c) > (?b > ?c) > ?c"
    systemT += bar2

    // add a term+type to represent the empty program
    val ty1 = ty"1"
    val tmi = hoc"i : 1"
    systemT += InductiveType( ty1, tmi )

    /*
    // With dependent types:
    val eq = ty"eq ?a"
    val refl = hoc"refl{?a}: ?a > (eq ?a)"
    systemT += InductiveType( eq, refl )
    */
    val eq = ty"eq"
    val refl = hoc"refl: eq"
    systemT += InductiveType( eq, refl )

    /*
    // With dependent types:
    val subst = hoc"subst{?a}: (eq ?a) > ((?a > o) > (?a > o))"
    val t1: Expr = hov"t1: ?a"
    val t2: Expr = hov"t2: ?a > o"
    systemT += PrimRecFun( List(
      ( subst, List(
        //( refl( p, refl( t1, t2 ) ) -> p( t2 ) ),
        ( subst( refl( t1 ), t2 ) -> t2 ) ) ) ) )( systemT )
    */
    //val subst = hoc"subst{?a}: eq > (?a > ?a)"
    val subst = hoc"subst{?a}: 1 > (?a > ?a)"
    val t2: Expr = hov"t2: ?a"
    systemT += PrimRecFun( List(
      ( subst, List(
        //( subst( refl, t2 ) -> t2 ) ) ) ) )( systemT )
        ( subst( tmi, t2 ) -> t2 ) ) ) ) )( systemT )

    //println( "systemT" )
    //println( systemT )
    systemT
  }

  def extractCases( proof: NDProof )( implicit ctx: Context ): Expr = {
    val ng = new NameGenerator( freeVariables( proof.conclusion ).map( _.name ) )
    val lambda = extractCases( proof, ng )( systemT( ctx ) )
    val res = lambda.antecedent.fold( lambda( Suc( 0 ) ) )( ( agg, v ) => Abs( v.asInstanceOf[Var], agg ) )
    if ( !freeVariables( res ).isEmpty ) {
      //throw new Exception( s"free variables: ${freeVariables( res )}" )
    }
    println( res )
    println( "permuted:" )
    println( permuteEM( res )( systemT( ctx ) ) )
    res
  }

  def simplifyExpr( e: Expr )( implicit ctx: Context ): Expr = {
    e match {
      case t @ App( Const( "pi1", _, List( tyL, tyR ) ), arg ) =>
        if ( tyL != ty"1" && tyR != ty"1" ) {
          t
        } else if ( tyL == ty"1" ) {
          le"i"
        } else {
          arg
        }
      case t @ App( Const( "pi2", _, List( tyL, tyR ) ), arg ) =>
        if ( tyL != ty"1" && tyR != ty"1" ) {
          t
        } else if ( tyR == ty"1" ) {
          le"i"
        } else {
          arg
        }
      case t @ App( t1, t2 ) if t1.ty != ty"1" && t2.ty != ty"1" => t
      case App( _, t2 ) if t2.ty == ty"1"                        => le"i"
      case App( t1, t2 ) if t1.ty == ty"1" && t2.ty != ty"1"     => t1
    }
  }

  def extractCases( proof: NDProof, ng: NameGenerator )( implicit systemT: Context ): Sequent[Expr] = {

    val res =
      proof match {
        case WeakeningRule( subProof, formula ) =>
          val s = extractCases( subProof, ng )
          val v = getVar( "v", formula, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
          val res = v +: s
          //println( "Weakening, fresh " + v )
          res

        case ContractionRule( subProof, aux1, aux2 ) =>
          val s = extractCases( subProof, ng )
          val v = s( aux1 )
          val res = v +: s.delete( List( aux1, aux2 ) )
          //println( "Contraction" )
          res

        /*
        case LogicalAxiom( formula @ All( x, f ) ) if x.ty == ty"i" =>
          // TODO:
          val a = Var( ng.fresh( "a" ), flat( formula ) )
          val h = Const( ng.fresh( "H" ), flat( formula ) )
          val res = a +: Sequent() :+ h
          //println( "Axiom All " + formula + ", fresh a " + a + " fresh H " + h )
          res

        case LogicalAxiom( formula @ Ex( x, Neg( f ) ) ) if x.ty == ty"i" =>
          // TODO:
          val a = Var( ng.fresh( "a" ), flat( formula ) )
          val w = Const( ng.fresh( "W" ), flat( formula ) )
          val res = a +: Sequent() :+ w
          //println( "Axiom Ex Neg " + formula + ", fresh a " + a + " fresh W " + w )
          res

        case LogicalAxiom( formula ) if !containsQuantifierOnLogicalLevel( formula ) =>
          val a = Var( ng.fresh( "a" ), flat( formula ) )
          val h = Const( ng.fresh( "H" ), flat( formula ) )
          val res = a +: Sequent() :+ h
          //println( "LogicalAxiom propositional " + formula + ", fresh a " + a + " fresh H " + h )
          res
        */

        case LogicalAxiom( formula ) =>
          //val v = Var( ng.fresh( "v" ), flat( formula ) )
          val v = getVar( "v", formula, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
          val res = v +: Sequent() :+ v
          //println( "LogicalAxiom " + formula + ", fresh v " + v )
          res

        case AndElim1Rule( subProof ) =>
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), le"pi1(${s( Suc( 0 ) )})" )
          //println( "AndElim1" )
          res

        case AndElim2Rule( subProof ) =>
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), le"pi2(${s( Suc( 0 ) )})" )
          //println( "AndElim2" )
          res

        case AndIntroRule( leftSubProof, rightSubProof ) =>
          val l = extractCases( leftSubProof, ng )
          val r = extractCases( rightSubProof, ng )
          // TODO: order
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"pair(${l( Suc( 0 ) )},${r( Suc( 0 ) )})"
          //println( "AndIntro" )
          res

        case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
          val l = extractCases( leftSubProof, ng )
          val m = extractCases( middleSubProof, ng )
          val r = extractCases( rightSubProof, ng )
          val varA = m( aux1 ).asInstanceOf[Var]
          val varB = r( aux2 ).asInstanceOf[Var]
          // TODO: order
          val res = l.antecedent ++: m.delete( aux1 ).antecedent ++: r.delete( aux2 ).antecedent ++: Sequent() :+
            le"matchSum( ${
              l( Suc( 0 ) )
            },${
              Abs( varA, m( Suc( 0 ) ) )
            },${
              Abs( varB, r( Suc( 0 ) ) )
            })"
          //println( "OrElim" )
          res

        case OrIntro1Rule( subProof, rightDisjunct ) =>
          val leftType = flat( subProof.endSequent( Suc( 0 ) ) )
          val rightType = flat( rightDisjunct )
          val inl = systemT.constant( "inl", List( leftType, rightType ) ).get
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), inl( s( Suc( 0 ) ) ) )
          //println( "OrIntro1" )
          res

        case OrIntro2Rule( subProof, leftDisjunct ) =>
          val leftType = flat( leftDisjunct )
          val rightType = flat( subProof.endSequent( Suc( 0 ) ) )
          val inr = systemT.constant( "inr", List( leftType, rightType ) ).get
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), inr( s( Suc( 0 ) ) ) )
          //println( "OrIntro2" )
          res

        case ImpElimRule( leftSubProof, rightSubProof ) =>
          val l = extractCases( leftSubProof, ng )
          val r = extractCases( rightSubProof, ng )

          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )
          val t = App( l( Suc( 0 ) ), r( Suc( 0 ) ) )
          val ts = simplifyExpr( t )
          println( s"t: $t" )
          println( s"ts: $ts" )
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ ts
          //println( "ImpElim" )
          res

        case ImpIntroRule( subProof, aux ) =>
          val s = extractCases( subProof, ng )
          val extraVar = s( aux ).asInstanceOf[Var]

          /*
          // From ContextRule, order of premises in {Binary, Ternary}NDRule
          // mainFormulaSequent like in rule case classes
          val formulasToBeDeleted = List(aux)
          val premises = List(s)
          val contexts = for ( ( p, is ) <- premises zip formulasToBeDeleted ) yield p.delete( is )
          val mainFormulaSequent = Sequent() :+ Abs( extraVar, s( Suc( 0 ) ) )

          mainFormulaSequent.antecedent ++: contexts.flattenS :++ mainFormulaSequent.succedent
          */
          //println( "ImpIntro deleting: " + s( aux ) + " of type " + s( aux ).ty )
          val res = s.delete( aux ).antecedent ++: Sequent() :+ Abs( extraVar, s( Suc( 0 ) ) )
          //println( "ImpIntro" )
          res

        case NegElimRule( leftSubProof, rightSubProof ) =>
          val l = extractCases( leftSubProof, ng )
          val r = extractCases( rightSubProof, ng )
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )
          //println( "NegElim" )
          res

        // TODO: I think NegIntroRule should produce a term of type ?a > (exn ?a)
        case NegIntroRule( subProof, aux ) =>
          val s = extractCases( subProof, ng )
          val extraVar = s( aux ).asInstanceOf[Var]
          val res = s.delete( aux ).antecedent ++: Sequent() :+ Abs( extraVar, s( Suc( 0 ) ) )
          //println( "NegIntro" )
          res
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
          // TODO
          Sequent() :+ le"i"
        //val varr = Var( "z", ty"1" )
        //Abs( varr, varr )

        case BottomElimRule( subProof, mainFormula ) =>
          val s = extractCases( subProof, ng )
          // TODO is this true in general?
          /*
          val exnTypeParameter = s( Suc( 0 ) ).ty match {
            case TBase( "exn", param :: Nil ) => param
            case _                            => throw new Exception( "Realizer must be of type exn ?a." )
          }
          */

          /*
        val tmp = subProofRealizer match {
          case Abs.Block( _, e ) =>
            e.ty match {
              case TBase( "exn", param :: Nil ) => param
              case _                            => throw new Exception( "Realizer must be of type exn ?a." )
            }
        }
        */

          val efqType = flat( mainFormula )
          //val raise = systemT.constant( "raise", List( exnTypeParameter, raisedType ) ).get
          val efq = systemT.constant( "efq", List( efqType ) ).get
          // TODO reverse makes App in ExcludedMiddle realizer work (example6)
          // TODO reverse makes App in ExcludedMiddle realizer fail (example7)
          //Abs( variablesAntConclusion( proof ).reverse, raise( App( subProofRealizer, variablesAntPremise( proof, 0 ) ) ) )
          val res = s.replaceAt( Suc( 0 ), efq( s( Suc( 0 ) ) ) )
          //println( "BottomElim" )
          res

        case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), Abs( eigenVariable, s( Suc( 0 ) ) ) )
          //println( "AllIntro" )
          res

        case ForallElimRule( subProof, term ) =>
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), App( s( Suc( 0 ) ), term ) )
          //println( "AllElim" )
          res

        case ExistsIntroRule( subProof, formula, term, variable ) =>
          val s = extractCases( subProof, ng )
          val res = s.replaceAt( Suc( 0 ), le"pair($term,${s( Suc( 0 ) )})" )
          //println( "ExIntro" )
          res

        case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
          val l = extractCases( leftSubProof, ng )
          val r = extractCases( rightSubProof, ng )

          val sub1 = Substitution( eigenVariable, le"pi1(${l( Suc( 0 ) )})" )
          //val extraVar = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux ) ) )
          // use deleted var instead of fresh one
          val extraVar = r( aux ).asInstanceOf[Var]
          val sub2 = Substitution( extraVar, le"pi2(${l( Suc( 0 ) )})" )
          val res = l.antecedent ++: r.delete( aux ).antecedent ++: Sequent() :+ sub1( sub2( r( Suc( 0 ) ) ) )
          //println( "ExElim extraVar " + extraVar )
          res

        case TheoryAxiom( mainFormula ) =>
          val res = Sequent() :+ Var( ng.fresh( s"realizer($mainFormula)" ), flat( mainFormula ) )
          res

        case eq @ EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
          // TODO
          //mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )
          val l = extractCases( leftSubProof, ng )
          val r = extractCases( rightSubProof, ng )
          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ Var( ng.fresh( s"eq(${eq.mainFormula})" ), flat( eq.mainFormula ) )
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"subst ${l( Suc( 0 ) )} ${r( Suc( 0 ) )}"
          //le"eq(${l( Suc( 0 ) )}, ${r( Suc( 0 ) )})" // ), flat( eq.mainFormula ) )
          //println( "EqElim" )
          res

        case eq @ EqualityIntroRule( term ) =>
          // TODO
          //val res = Sequent() :+ Var( ng.fresh( s"True" ), flat( eq.mainFormula ) )
          //val res = Sequent() :+ le"refl $term"
          //val res = Sequent() :+ le"refl"
          val res = Sequent() :+ le"i"
          //le"eq($term, $term)"
          //println( "EqIntro" )
          res

        // Works only for the type of natural numbers at the moment
        // Assumes that the induction cases for the constructors are in the same order as the inductive type definition in the context.
        case InductionRule( cases, formula, term ) =>
          val baseCase = extractCases( cases( 0 ).proof, ng )
          val inductionCase = extractCases( cases( 1 ).proof, ng )
          // TODO same for base case, should be empty in our case
          val inductionCaseDel = inductionCase.delete( cases( 1 ).hypotheses )
          /*
          println( "free vars inductionCase ant 0: " + freeVariables( inductionCase( cases( 1 ).hypotheses ).filter( e => e.ty == ty"i" ) ) )
          println( "free vars inductionCase suc 0: " + freeVariables( inductionCase( Suc( 0 ) ) ) )
          */
          val varsH = inductionCase( cases( 1 ).hypotheses ).asInstanceOf[Seq[Var]]
          println( "inductionCase hyps: " + inductionCase( cases( 1 ).hypotheses ) )
          println( "baseCase suc 0: " + baseCase( Suc( 0 ) ) )
          println( "inductionCase suc 0: " + inductionCase( Suc( 0 ) ) )
          println( "term: " + term )
          println( "cases 0: " + cases( 0 ).proof.endSequent )
          println( "cases 1: " + cases( 1 ).proof.endSequent )
          /*
          */
          val res = baseCase.antecedent ++: inductionCaseDel.antecedent ++: Sequent() :+
            le"natRec(${baseCase( Suc( 0 ) )})(${Abs( cases( 1 ).eigenVars, Abs( varsH, inductionCase( Suc( 0 ) ) ) )})($term)"
          //println( "InductionRule" )
          res

        // assuming that the definitionrule is applied according to rewrite rules of the original context
        case DefinitionRule( subProof, mainFormula ) =>
          ???
        /*
          val res = extractCases( subProof, ng )
          //println( "DefinitionRule" )
          res
          */

        case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
          leftSubProof.endSequent( aux1 ) match {
            case f @ Ex( x, g ) =>
              /*
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
              val tl = nd.ProofBuilder.
                c( leftSubProof ).
                u( ImpIntroRule( _, aux1 ) ).
                c( left ).
                b( ImpElimRule( _, _ ) ).
                qed
                */
              //val l = extractCases( tl, ng )
              val l = extractCases( leftSubProof, ng )

              /*
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

              val tr = nd.ProofBuilder.
                c( rightSubProof ).
                u( ImpIntroRule( _, aux2 ) ).
                c( right ).
                b( ImpElimRule( _, _ ) ).
                qed
                */
              /*
              println( "right Suc 0: " + right.conclusion( Suc( 0 ) ) )
              println( "rightSubProof aux2 " + rightSubProof.conclusion( aux2 ) )
              println( "tr: " + tr )
              //println( "right: " + extractCases( right, ng ) )
              println( "flat right" + flat( right.conclusion( Suc( 0 ) ) ) )
              */
              //val r = extractCases( tr, ng )
              val r = extractCases( rightSubProof, ng )
              //val varL = l( Ant( 0 ) ).asInstanceOf[Var]
              val varL = l( aux1 ).asInstanceOf[Var]
              //val varR = r.antecedent.last.asInstanceOf[Var]
              val varR = r( aux2 ).asInstanceOf[Var]

              /*
              println( "l.antecedent: " + l.antecedent )
              println( "r.antecedent: " + r.antecedent )
              println( "deleting l(aux1): " + l( aux1 ) )
              println( "deleting r(aux2): " + r( aux2 ) )

              println( "leftSubProof size: " + leftSubProof.endSequent.size )
              println( "tl size: " + tl.endSequent.size )
              println( "l size: " + l.size )
              */
              //val delL = l.delete( Ant( 0 ) ).antecedent
              val delL = l.delete( aux1 ).antecedent
              /*
              println( "delL size: " + delL.size )

              println( "rightSubProof size: " + rightSubProof.endSequent.size )
              println( "tr size: " + tr.endSequent.size )
              println( "r size: " + r.size )
              println( "r indices: " + r.indices )
              println( "r indices last: " + r.indicesSequent.antecedent.last )
              */

              // TODO find index to delete somehow
              //val delR = r.delete( r.indicesSequent.antecedent.last ).antecedent
              val delR = r.delete( aux2 ).antecedent
              /*
              println( "delR size: " + delR.size )
              */

              val res = delL ++: delR ++: Sequent() :+ le"bar2 ${Abs( x, g )} ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              println( s"EM1: ${f}, l(Suc(0)).ty: ${l( Suc( 0 ) ).ty}, r(Suc(0)).ty: ${r( Suc( 0 ) ).ty}" )
              println( s"EM1: ${f}, tyL: ${varL.ty}, tyR: ${varR.ty}" )
              println( "res type: " + res( Suc( 0 ) ).ty )
              /*
              println( "res size: " + res.size )
              */
              res

            case f =>
              val l = extractCases( leftSubProof, ng )
              val r = extractCases( rightSubProof, ng )
              val varL = l( aux1 ).asInstanceOf[Var]
              val varR = r( aux2 ).asInstanceOf[Var]
              val delL = l.delete( aux1 ).antecedent
              val delR = r.delete( aux2 ).antecedent
              val res = delL ++: delR ++: Sequent() :+ le"bar ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              //val res = l.delete( aux1 ).antecedent ++: r.delete( aux2 ).antecedent ++: Sequent() :+ le"bar ${l( Suc( 0 ) )} ${r( Suc( 0 ) )}"
              println( s"EM0: ${f}" )
              res
          }
      }
    if ( res.indices != proof.conclusion.indices ) {
      println( "BUG" )
      println( "res.indices: " + res.indices )
      println( "proof.conclusion.indices: " + proof.conclusion.indices )
      throw new Exception( s"$res != ${proof.conclusion}" )
    }
    if ( !res.zipWithIndex.forall { case ( e, i ) => e.ty == flat( proof.conclusion( i ) ) } ) {
      println( "BUG (type of program term doesn't match flat(proof term))" )
      res.zipWithIndex.filter { case ( e, i ) => e.ty != flat( proof.conclusion( i ) ) }.foreach { case ( e, i ) => println( s"$i\nactual: ${e.ty}\nexpected: ${flat( proof.conclusion( i ) )} (i.e. flat(${proof.conclusion( i )}))" ) }
      println( "proof.conclusion : " + proof.conclusion )
      println( "extracted program: " + res )
      throw new Exception()
    }
    res
  }

  def normalForm( ty: Ty )( implicit ctx: Context ) = ty match {
    case TBase( "conj", _ :: TBase( "1", Nil ) :: Nil )   => ty"1"
    case TBase( "conj", TBase( "1", Nil ) :: tau :: Nil ) => tau
    case _ ->: TBase( "1", Nil )                          => ty"1"
    case TBase( "1", Nil ) ->: tau                        => tau
  }

  // computes the type of a potential m-realizer for the formula
  def flat( formula: Formula )( implicit ctx: Context ): Ty = formula match {
    case Bottom() => ty"exn"
    case Top()    => ty"exn" ->: ty"exn"
    //case Eq( s, t )                       => ty"1"
    case Eq( s, _ ) =>
      // With dependent types:
      //TBase( "eq", TVar( s.toString ) )
      // Losing information of dependent types:
      //TBase( "eq" )
      ty"1"
    case Atom( e, es ) =>
      // With dependent types:
      //TBase( e.toUntypedString, es.map( x => TVar( x.toString ) ) )
      //TBase( e.toUntypedString, es.map( x => TBase( x.toString ) ) )
      // Losing information of dependent types:
      //TBase( e.toUntypedString )
      ty"1" // ?
    case And( leftformula, rightformula ) =>
      normalForm( TBase( "conj", flat( leftformula ), flat( rightformula ) ) )
    case Or( leftformula, rightformula ) =>
      normalForm( TBase( "sum", flat( leftformula ), flat( rightformula ) ) )
    case Imp( leftformula, rightformula ) =>
      normalForm( flat( leftformula ) ->: flat( rightformula ) )
    case Neg( subformula ) =>
      normalForm( flat( subformula ) ->: ty"exn" ) //TBase( "exn", flat( subformula ) ) //flat( Imp( subformula, Bottom() ) )
    case Ex( variable, subformula ) =>
      normalForm( TBase( "conj", variable.ty, flat( subformula ) ) )
    case All( variable, subformula ) =>
      normalForm( variable.ty ->: flat( subformula ) )
  }

  def permuteEM( term: Expr )( implicit ctx: Context ): Expr = {
    term match {
      case App( App( App( Const( "bar", _, _ ), u ), v ), w ) =>
        val wPermuted = permuteEM( w )
        le"bar (${permuteEM( u )}$wPermuted) (${permuteEM( v )}$wPermuted)"
      case App( Const( "pi1", _, _ ), App( App( Const( "bar2", _, _ ), u ), v ) ) =>
        le"bar (pi1 ${permuteEM( u )}) (pi1 ${permuteEM( v )})"
      case App( Const( "pi2", _, _ ), App( App( Const( "bar", _, _ ), u ), v ) ) =>
        le"bar (pi2 ${permuteEM( u )}) (pi2 ${permuteEM( v )})"
      case App( App( App( Const( "matchSum", _, _ ), App( App( Const( "bar", _, _ ), u ), v ) ), x ), y ) =>
        val uPermuted = permuteEM( u )
        val vPermuted = permuteEM( v )
        val xPermuted = permuteEM( x )
        val yPermuted = permuteEM( y )
        val ms1 = le"(matchSum $uPermuted $xPermuted $yPermuted)"
        val ms2 = le"(matchSum $vPermuted $xPermuted $yPermuted)"
        le"bar $ms1 $ms2"
      // Last case described in Federico's paper handled by substitution in ExistsElimRule case of extraction
      case App( App( App( App( Const( "bar2", _, _ ), p ), u ), v ), w ) =>
        val wPermuted = permuteEM( w )
        le"bar2 $p (${permuteEM( u )}$wPermuted) (${permuteEM( v )}$wPermuted)"
      case App( Const( "pi1", _, _ ), App( App( App( Const( "bar2", _, _ ), p ), u ), v ) ) =>
        le"bar2 $p (pi1 ${permuteEM( u )}) (pi1 ${permuteEM( v )})"
      case App( Const( "pi2", _, _ ), App( App( App( Const( "bar2", _, _ ), p ), u ), v ) ) =>
        le"bar2 $p (pi2 ${permuteEM( u )}) (pi2 ${permuteEM( v )})"
      case App( App( App( Const( "matchSum", _, _ ), App( App( App( Const( "bar2", _, _ ), p ), u ), v ) ), x ), y ) =>
        println( s"term: $term" )
        val Abs( uVar, uPermuted ) = permuteEM( u )
        val Abs( vVar, vPermuted ) = permuteEM( v )
        val xPermuted = permuteEM( x )
        val yPermuted = permuteEM( y )

        println( s"u: $u\np: $uPermuted" )
        println( s"v: $v\np: $vPermuted" )
        println( s"x: $x\np: $xPermuted" )
        println( s"y: $y\np: $yPermuted" )
        val ms1 = le"^$uVar (matchSum $uPermuted $xPermuted $yPermuted)"
        val ms2 = le"^$vVar (matchSum $vPermuted $xPermuted $yPermuted)"
        println( s"ms1: $ms1" )
        println( s"ms2: $ms2" )
        // TODO: bar2 p ms1 m1 type checks
        le"bar2 $p $ms1 $ms2"
      // Last case described in Federico's paper handled by substitution in ExistsElimRule case of extraction
      case _ => term
    }
  }
}

class ClassicalExtractionCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

