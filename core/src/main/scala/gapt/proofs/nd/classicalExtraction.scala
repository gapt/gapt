package gapt.proofs.nd

import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.expr.{ App, Substitution, Ty, typeVariables, _ }
import gapt.proofs.context.Context
import gapt.proofs._
import gapt.proofs.context.facet.{ BaseTypes, StructurallyInductiveTypes }
import gapt.proofs.context.update.{ InductiveType, PrimitiveRecursiveFunction, ReductionRuleUpdate }
import gapt.utils.NameGenerator

import scala.collection.mutable

object ClassicalExtraction {

  private val varMap: mutable.Map[Formula, Var] = mutable.Map.empty
  private def getVar( f: Formula, nameGenerator: NameGenerator )( implicit ctx: Context ) = {
    val name = "vLambda"
    if ( varMap.contains( f ) ) {
      varMap( f )
    } else {
      val v = Var( nameGenerator.fresh( name ), flat( f ) )
      varMap += ( f -> v )
      v
    }
  }

  def getVarMap = varMap

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

      systemT += PrimitiveRecursiveFunction( recursor, equations )
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
    systemT += PrimitiveRecursiveFunction(
      pi1,
      List( ( pi1( pair( x, y ) ) -> x ) ) )( systemT )
    systemT += PrimitiveRecursiveFunction(
      pi2,
      List( ( pi2( pair( x, y ) ) -> y ) ) )( systemT )

    // add sum type
    val sum = ty"sum ?a ?b"
    val inl = hoc"inl{?a ?b}: ?a > (sum ?a ?b)"
    val inr = hoc"inr{?a ?b}: ?b > (sum ?a ?b)"
    systemT += InductiveType( sum, inl, inr )
    val matchSum = hoc"matchSum{?a ?b ?c}: (sum ?a ?b) > (?a > ?c) > (?b > ?c) > ?c"
    val w1: Expr = hov"w1: ?a > ?c"
    val w2: Expr = hov"w2: ?b > ?c"
    systemT += PrimitiveRecursiveFunction(
      matchSum,
      List(
        ( matchSum( inl( x ), w1, w2 ) -> w1( x ) ),
        ( matchSum( inr( y ), w1, w2 ) -> w2( y ) ) ) )( systemT )

    val existsElim = hoc"existsElim{?a ?b ?c}: (exconj ?a ?b) > (?a > ?b > ?c) > ?c"
    val w3: Expr = hov"w3: ?a > ?b > ?c"
    val exconj = ty"exconj ?a ?b"
    val expair = hoc"expair{?a ?b}: ?a > ?b > (exconj ?a ?b)"
    systemT += InductiveType( exconj, expair )

    val catchConst = hoc"catch{?a ?b}: o > (exconj ?a ?b) > (exconj ?a ?b)"
    systemT += catchConst
    val q = hof"q: o"

    systemT += PrimitiveRecursiveFunction(
      existsElim,
      List(
        ( existsElim( expair( x, y ), w3 ) -> w3( x )( y ) ),
        ( existsElim( catchConst( q, expair( x, y ) ), w3 ) -> w3( x )( y ) ) ) )( systemT )
    val expi1 = hoc"expi1{?a ?b}: (exconj ?a ?b) > ?a"
    val expi2 = hoc"expi2{?a ?b}: (exconj ?a ?b) > ?b"
    systemT += PrimitiveRecursiveFunction(
      expi1,
      List( ( expi1( expair( x, y ) ) -> x ) ) )( systemT )
    systemT += PrimitiveRecursiveFunction(
      expi2,
      List( ( expi2( expair( x, y ) ) -> y ) ) )( systemT )

    //val bar = hoc"bar{?a}: ?a > ?a > hyp > ?a"
    //val hyp = ty"hyp"
    //systemT += InductiveType( hyp, bar )

    /*
    val exn = ty"exn ?a"
    val exception = hoc"exception{?a}: ?a > (exn ?a)"
    systemT += InductiveType( exn, exception )
    val efq = hoc"efq{?a ?c}: (exn ?a) > ?c"
    systemT += efq
    val handle = hoc"handle{?a ?c}: (exn ?a) > ?c > (?a > ?c)"
    systemT += handle
    */
    val exn = TBase( "exn" )
    val exception = hoc"exception{?a}: ?a > exn"
    systemT += exn
    systemT += exception
    val efq = hoc"efq{?c}: exn > ?c"
    systemT += efq
    /*
    val handle = hoc"handle{?a ?c}: exn > ?c > (?a > ?c)"
    systemT += handle
    systemT += PrimRecFun(
      handle,
      List( ( handle( exception( x ), w1 ) -> w1( x ) ) ) )( systemT )
      */
    //systemT += efq
    //val raise = hoc"raise{?a}: ?a > exn"
    //systemT += raise
    //val e = hoc"e: exn ?a"
    /*
    systemT += PrimRecFun( List(
      ( efq, List(
        ( le"(efq( e )) x" -> le"efq( e )" ) ) ) ) )( systemT )
    //( le"efq{(exn ?a) ?b}( efq( e ) )" -> le"efq{(exn ?a) ?b}( e )" ) ) ) ) )( systemT )
    */
    /*
    val e: Expr = Var( "e", exn )
    systemT += PrimRecFun( List(
      ( raise, List(
        //( raise( e )( y ) -> raise( e ) ) ) ) ) )( systemT )
        ( raise( raise( e ) ) -> raise( e ) ) ) ) ) )( systemT )
    */

    //val handle = hoc"handle{?a ?b}: (?a > ?b) > ((?a > (exn ?a)) > ?b) > ?b"
    //val tryCatch = hoc"tryCatch{?a ?c}: ((?a > exn) > ?c) > (?a > ?c) > ?c"
    val tryConst = hoc"try{?a ?b}: o > (?a > (?b > exn)) > (?a > (?b > exn))"
    systemT += tryConst
    val tryCatch = hoc"tryCatch{?a ?b ?c}: ?a > ?b > ?c > ?c > ?c"
    systemT += tryCatch
    /*
    val w5 = hov"w5:?a"
    systemT += PrimRecFun(
      em,
      List( ( em( handle( exception( x ), w1 ), ( efq( exception( w5 ) ) ) ) -> w1( w5 ) ) ) )( systemT )
      */

    // add a term+type to represent the empty program
    val ty1 = ty"1"
    val tmi = hoc"i : 1"
    systemT += InductiveType( ty1, tmi )

    /*
    // With dependent types:
    val eq = ty"eq ?a"
    val refl = hoc"refl{?a}: ?a b (eq ?a)"
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
    /*
    //val subst = hoc"subst{?a}: eq > (?a > ?a)"
    val subst = hoc"subst{?a}: 1 > (?a > ?a)"
    val t2: Expr = hov"t2: ?a"
    systemT += PrimRecFun( List(
      ( subst, List(
        //( subst( refl, t2 ) -> t2 ) ) ) ) )( systemT )
        ( subst( tmi, t2 ) -> t2 ) ) ) ) )( systemT )
    */

    //println( "systemT" )
    //println( systemT )
    //val cmp = hoc"cmp: nat>nat>sum(sum(1)(1))(1)"

    val u: Expr = hov"u : nat"
    val v: Expr = hov"v : nat"
    val Some( inl1 ) = systemT.constant( "inl", List( ty"sum(1)(1)", ty"1" ) )
    val Some( inl2 ) = systemT.constant( "inl", List( ty"1", ty"1" ) )
    val Some( inr1 ) = systemT.constant( "inr", List( ty"sum(1)(1)", ty"1" ) )
    val Some( inr2 ) = systemT.constant( "inr", List( ty"1", ty"1" ) )
    val Some( i ) = systemT.constant( "i" )
    val Some( z ) = systemT.constant( "0" )
    val Some( s ) = systemT.constant( "s" )
    val pred = hoc"pred: nat>nat"
    systemT += PrimitiveRecursiveFunction(
      pred,
      List(
        pred( s( u ) ) -> u,
        pred( z ) -> z ) )
    val subtr = hoc"subtr: nat>nat>nat"
    systemT += PrimitiveRecursiveFunction(
      subtr,
      List(
        subtr( u )( z ) -> u,
        subtr( u )( s( v ) ) -> subtr( pred( u ) )( v ) ) )
    val x1: Expr = hov"x1 : ?a"
    val x2: Expr = hov"x2 : ?a"
    val x3: Expr = hov"x3 : o"
    val Some( trueC ) = systemT.constant( "⊤" )
    val Some( falseC ) = systemT.constant( "⊥" )
    val ite = hoc"ite{?a}:o>?a>?a>?a"
    systemT += PrimitiveRecursiveFunction(
      ite,
      List(
        ite( trueC )( x1 )( x2 ) -> x1,
        ite( falseC )( x1 )( x2 ) -> x2 ) )
    import gapt.proofs.context.update.ReductionRuleUpdate._
    systemT += ReductionRule( hof"(true & x) = x" )
    systemT += ReductionRule( hof"(false & x) = false" )
    systemT += ReductionRule( hof"(x & true) = x" )
    systemT += ReductionRule( hof"(x & false) = false" )
    systemT += ReductionRule( hof"(-true) = false" )
    systemT += ReductionRule( hof"(-false) = true" )
    systemT += ReductionRule( hof"(x | true) = true" )
    systemT += ReductionRule( hof"(false | x) = x" )
    systemT += ReductionRule( hof"(x | false) = x" )
    systemT += ReductionRule( hof"(true -> x) = x" )
    systemT += ReductionRule( hof"(false -> x) = true" )
    val sg = hoc"sg: nat>o"
    systemT += PrimitiveRecursiveFunction(
      sg,
      List(
        sg( z ) -> falseC,
        sg( s( u ) ) -> trueC ) )
    val gt = hoc"gt: nat>nat>o"
    systemT += PrimitiveRecursiveFunction(
      gt,
      List(
        gt( z )( v ) -> sg( subtr( z )( v ) ),
        gt( s( u ) )( v ) -> sg( subtr( s( u ) )( v ) ) ) )
    val Some( ite1 ) = systemT.constant( "ite", List( ty"sum(sum(1)(1))(1)" ) )
    val cmp = hoc"cmp: nat>nat>sum(sum(1)(1))(1)"
    systemT += PrimitiveRecursiveFunction(
      cmp,
      List(
        cmp( z )( v ) ->
          ite1( gt( v )( z ) )( inl1( inl2( i ) ) /*v>u*/ )(
            ite1( gt( z )( v ) )( inl1( inr2( i ) ) /*u>v*/ )( inr1( i ) /*v=u*/ ) ),
        cmp( s( u ) )( v ) ->
          ite1( gt( v )( s( u ) ) )( inl1( inl2( i ) ) /*v>u*/ )(
            ite1( gt( s( u ) )( v ) )( inl1( inr2( i ) ) /*u>v*/ )( inr1( i ) /*v=u*/ ) ) ) )
    val Some( ite2 ) = systemT.constant( "ite", List( ty"sum(1)(1)" ) )
    val cmp2 = hoc"cmp2: nat>nat>sum(1)(1)"
    systemT += PrimitiveRecursiveFunction(
      cmp2,
      List(
        cmp2( z )( v ) ->
          ite2( gt( v )( z ) )( inr2( i ) )( inl2( i ) ),
        cmp2( s( u ) )( v ) ->
          ite2( gt( v )( s( u ) ) )( inr2( i ) )( inl2( i ) ) ) )
    systemT
  }

  def extractCases( proof: NDProof )( implicit ctx: Context ): Expr = {
    val evs = proof.subProofs.collect {
      case ForallIntroRule( _, ev, _ )  => Seq( ev )
      case InductionRule( cases, _, _ ) => cases( 1 ).eigenVars
    }.flatten.map( _.name )
    val ng = new NameGenerator( evs )
    val lambda = extractCases( proof, ng, Map.empty, Map.empty ) //systemT( ctx ) )
    //val res = lambda( Suc( 0 ) )
    //lambda.antecedent.foreach( e => println( s"abstracting ${e.asInstanceOf[Var]}" ) )
    val res = lambda.antecedent.fold( lambda( Suc( 0 ) ) )( ( agg, v ) => Abs( v.asInstanceOf[Var], agg ) )
    if ( !freeVariables( res ).isEmpty ) {
      //throw new Exception( s"free variables: ${freeVariables( res )}" )
    }
    //println( s"before remove empty program and permute em:\n$res" )
    //println( "permuted:" )
    //println( permuteEM( res )( systemT( ctx ) ) )
    //permuteEM( remEmpProg( res ) )
    //permuteEM( res )
    //permuteEM( res )
    //normalize( res )
    //remEmpProg( res )
    res
  }

  def extractCases( proof: NDProof, ng: NameGenerator, exEm1HypVars: Map[Formula, Var], forallEm1HypVars: Map[Formula, Var] )( implicit systemT: Context ): Sequent[Expr] = {

    val res =
      proof match {
        case WeakeningRule( subProof, formula ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val v = getVar( formula, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
          val res = v +: s
          //println( "Weakening, fresh " + v )
          res

        case ContractionRule( subProof, aux1, aux2 ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          assert( s( aux1 ) == s( aux2 ) )
          val v = s( aux1 )
          val res = v +: s.delete( List( aux1, aux2 ) )
          //println( "Contraction" )
          res

        /*
        case LogicalAxiom( formula @ Neg( Ex( _, p ) ) ) =>
          // TODO:
          val a = getVar( "vHyp", formula, ng )
          val h = Const( "raise", flat( formula ) )
          val res = a +: Sequent() :+ h
          //println( "Axiom All " + formula + ", fresh a " + a + " fresh H " + h )
          res

        case LogicalAxiom( formula @ Ex( _, p ) ) =>
          // TODO:
          val a = getVar( "vHyp", formula, ng )
          val res = a +: Sequent() :+ a
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
          /*
          val v = formula match {
            case Neg( f ) => {
              val v = getVar( "v", f, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
              le"^$v exception $v"
            }
            case f => {
              getVar( "v", f, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
            }
          }
          */
          val res = if ( forallEm1HypVars.contains( formula ) ) {
            println( "nonempty" )
            val All( alpha, Neg( p ) ) = formula
            val tryConst = systemT.constant( "try", List( alpha.ty, flat( p ) ) ).get
            val a = forallEm1HypVars( formula )
            a +: Sequent() :+ tryConst( formula, a )

          } else if ( exEm1HypVars.contains( formula ) ) {
            println( "nonempty" )
            val Ex( alpha, p ) = formula
            val catchConst = systemT.constant( "catch", List( alpha.ty, flat( p ) ) ).get
            val a = exEm1HypVars( formula )
            a +: Sequent() :+ catchConst( formula, a )
          } else {
            val v = getVar( formula, ng ) //Var( ng.fresh( "y" ), flat( formula ) )
            v +: Sequent() :+ v
          }
          //println( "LogicalAxiom " + formula + ", fresh v " + v )
          res

        case AndElim1Rule( subProof ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), le"pi1(${s( Suc( 0 ) )})" )
          //println( "AndElim1" )
          res

        case AndElim2Rule( subProof ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), le"pi2(${s( Suc( 0 ) )})" )
          //println( "AndElim2" )
          res

        case AndIntroRule( leftSubProof, rightSubProof ) =>
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )
          // TODO: order
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"pair(${l( Suc( 0 ) )},${r( Suc( 0 ) )})"
          //println( "AndIntro" )
          res

        case OrElimRule( leftSubProof, middleSubProof, aux1, rightSubProof, aux2 ) =>
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val m = extractCases( middleSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )
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
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), inl( s( Suc( 0 ) ) ) )
          //println( "OrIntro1" )
          res

        case OrIntro2Rule( subProof, leftDisjunct ) =>
          val leftType = flat( leftDisjunct )
          val rightType = flat( subProof.endSequent( Suc( 0 ) ) )
          val inr = systemT.constant( "inr", List( leftType, rightType ) ).get
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), inr( s( Suc( 0 ) ) ) )
          //println( "OrIntro2" )
          res

        case ImpElimRule( leftSubProof, rightSubProof ) =>
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )

          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )
          //println( "ImpElim" )
          res

        case ImpIntroRule( subProof, aux ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
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
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ App( l( Suc( 0 ) ), r( Suc( 0 ) ) )
          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"exception ${r( Suc( 0 ) )}"
          //println( "NegElim" )
          res

        // TODO: I think NegIntroRule should produce a term of type ?a > (exn ?a)
        case NegIntroRule( subProof, aux ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
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

        case TopIntroRule =>
          // TODO
          Sequent() :+ le"i"
        //val varr = Var( "z", ty"1" )
        //Abs( varr, varr )

        case BottomElimRule( subProof, mainFormula ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
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
          //val TBase( "exn", List( exnType ) ) = s( Suc( 0 ) ).ty
          val efqType = flat( mainFormula )
          //val raise = systemT.constant( "raise", List( exnTypeParameter, raisedType ) ).get
          val efq = systemT.constant( "efq", List( efqType ) ).get
          // TODO reverse makes App in ExcludedMiddle realizer work (example6)
          // TODO reverse makes App in ExcludedMiddle realizer fail (example7)
          //Abs( variablesAntConclusion( proof ).reverse, raise( App( subProofRealizer, variablesAntPremise( proof, 0 ) ) ) )
          println( s"raising efq: ${s( Suc( 0 ) )}" )
          val res = s.replaceAt( Suc( 0 ), efq( s( Suc( 0 ) ) ) )
          //println( "BottomElim" )
          res

        case ForallIntroRule( subProof, eigenVariable, quantifiedVariable ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), Abs( eigenVariable, s( Suc( 0 ) ) ) )
          //println( s"AllIntro, $eigenVariable, $quantifiedVariable" )
          res

        case ForallElimRule( subProof, term ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val res = s.replaceAt( Suc( 0 ), App( s( Suc( 0 ) ), term ) )
          //println( "AllElim" )
          res

        case ExistsIntroRule( subProof, formula, term, variable ) =>
          val s = extractCases( subProof, ng, exEm1HypVars, forallEm1HypVars )
          val subst = Substitution( variable, term )( formula )
          val res = s.replaceAt( Suc( 0 ), le"expair($term,${s( Suc( 0 ) )})" )
          val t = res( Suc( 0 ) )
          println( "ExIntro" )
          println( res( Suc( 0 ) ) )
          res

        case ExistsElimRule( leftSubProof, rightSubProof, aux, eigenVariable ) =>
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )

          //val sub1 = Substitution( eigenVariable, le"expi1(${l( Suc( 0 ) )})" )
          //val extraVar = Var( ng.fresh( "y" ), flat( rightSubProof.conclusion( aux ) ) )
          // use deleted var instead of fresh one
          val extraVar = r( aux ).asInstanceOf[Var]
          //val sub2 = Substitution( extraVar, le"expi2(${l( Suc( 0 ) )})" )
          //val res = l.antecedent ++: r.delete( aux ).antecedent ++: Sequent() :+ sub1( sub2( r( Suc( 0 ) ) ) )
          val param2 = le"^$eigenVariable (^$extraVar ${r( Suc( 0 ) )})"
          val res = l.antecedent ++: r.delete( aux ).antecedent ++: Sequent() :+ le"existsElim(${l( Suc( 0 ) )}, $param2)"
          //println( "ExElim extraVar " + extraVar )
          res

        case TheoryAxiom( mainFormula ) =>
          val res = Sequent() :+ Var( ng.fresh( s"realizer($mainFormula)" ), flat( mainFormula ) )
          res

        case eq @ EqualityElimRule( leftSubProof, rightSubProof, formulaA, variablex ) =>
          // TODO
          //mrealizeCases( rightSubProof, varsAntPrem( proof, variables, 1 ), ng )
          val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
          val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )
          println( "l: " + l )
          println( "r: " + r )
          println( Var( ng.fresh( s"eq(${eq.mainFormula})" ), flat( eq.mainFormula ) ).ty )
          val res = l.antecedent ++: r.antecedent ++: Sequent() :+ r.succedent.head
          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ Var( ng.fresh( s"eq(${eq.mainFormula})" ), flat( eq.mainFormula ) )
          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"subst ${l( Suc( 0 ) )} ${r( Suc( 0 ) )}"
          //val res = l.antecedent ++: r.antecedent ++: Sequent() :+ le"i"
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
          val baseCase = extractCases( cases( 0 ).proof, ng, exEm1HypVars, forallEm1HypVars )
          val inductionCase = extractCases( cases( 1 ).proof, ng, exEm1HypVars, forallEm1HypVars )
          // TODO same for base case, should be empty in our case
          val inductionCaseDel = inductionCase.delete( cases( 1 ).hypotheses )
          /*
          println( "free vars inductionCase ant 0: " + freeVariables( inductionCase( cases( 1 ).hypotheses ).filter( e => e.ty == ty"i" ) ) )
          println( "free vars inductionCase suc 0: " + freeVariables( inductionCase( Suc( 0 ) ) ) )
          */
          val varsH = inductionCase( cases( 1 ).hypotheses ).asInstanceOf[Seq[Var]]
          println( s"varsH: $varsH, ${cases( 1 ).proof.endSequent( cases( 1 ).hypotheses )}" )
          /*
          println( "inductionCase hyps: " + inductionCase( cases( 1 ).hypotheses ) )
          println( "baseCase suc 0: " + baseCase( Suc( 0 ) ) )
          println( "inductionCase suc 0: " + inductionCase( Suc( 0 ) ) )
          println( "term: " + term )
          println( "cases 0: " + cases( 0 ).proof.endSequent )
          println( "cases 1: " + cases( 1 ).proof.endSequent )
          */
          val res = baseCase.antecedent ++: inductionCaseDel.antecedent ++: Sequent() :+
            le"natRec(${baseCase( Suc( 0 ) )})(${Abs( cases( 1 ).eigenVars, Abs( varsH, inductionCase( Suc( 0 ) ) ) )})($term)"
          //println( "InductionRule" )
          res

        // assuming that the definitionrule is applied according to rewrite rules of the original context
        case DefinitionRule( subProof, mainFormula ) =>
          throw new Exception( "DefinitionRule not supported in classical extraction, use \"eliminateDefinitions\"." )

        case ExcludedMiddleRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
          leftSubProof.endSequent( aux1 ) match {
            /*
            case f @ All( x1, Ex( x2, g ) ) if !containsQuantifierOnLogicalLevel( g ) =>
              val l = extractCases( leftSubProof, ng )
              val r = extractCases( rightSubProof, ng )
              val varL = l( aux1 ).asInstanceOf[Var]
              val varR = r( aux2 ).asInstanceOf[Var]
              assert( varL.ty ->: ty"exn" == varR.ty )
              // TODO find index to delete somehow
              val delL = l.delete( aux1 ).antecedent
              val delR = r.delete( aux2 ).antecedent
              // TODO
              //val res = delL ++: delR ++: Sequent() :+ le"bar3 ${Abs( x1, Ex( x2, g ) )} ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              val res = delL ++: delR ++: Sequent() :+ le"tryCatch ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              res
              */
            case f @ Ex( x, g ) if !containsQuantifierOnLogicalLevel( g ) =>
              val exHypVar = ng.fresh( "aLambda" )
              val forallHypVar = ng.fresh( "aLambda" )

              val exEm1FormulasPrime = exEm1HypVars + ( Ex( x, g ) -> Var( exHypVar, flat( Ex( x, g ) ) ) )
              val forallEm1HypVarsPrime = forallEm1HypVars + ( All( x, -g ) -> Var( forallHypVar, flat( All( x, -g ) ) ) )

              val l = extractCases( leftSubProof, ng, exEm1FormulasPrime, forallEm1HypVarsPrime )
              val r = extractCases( ProofBuilder.
                c( rightSubProof ).
                u( ImpIntroRule( _, aux2 ) ).
                c( gapt.proofs.nd.LogicalAxiom( Ex( x, g ) ) ). //hof"?x -P(x)" ) ).
                c( gapt.proofs.nd.LogicalAxiom( All( x, -g ) ) ). //hof"!x P(x)" ) ).
                u( ForallElimRule( _, x ) ). //le"x:nat" ) ).
                c( gapt.proofs.nd.LogicalAxiom( g ) ). //hof"-P(x)" ) ).
                b( NegElimRule( _, _ ) ).
                b( ExistsElimRule( _, _ ) ).
                u( NegIntroRule( _, Ex( x, g ) ) ). //hof"?x -P(x)")).
                b( ImpElimRule( _, _ ) ).
                //  qed, ng, exEm1FormulasPrime, forallEm1HypVarsPrime )
                qed, ng, exEm1HypVars, forallEm1HypVarsPrime )

              val newAux2 = r.find( _.ty == flat( All( x, -g ) ) ).get

              val varL = l( aux1 ).asInstanceOf[Var]
              val varR = r( newAux2 ).asInstanceOf[Var]
              println( leftSubProof.endSequent( aux1 ) )
              println( rightSubProof.endSequent( newAux2 ) )

              //val rNew = normalize(le"(^$varR ${r(Suc(0))}) ${allRight(Suc(0))}")
              /*
              varR.ty match {
                case TArr( varL.ty, TBase( "exn", varL.ty ) ) => assert( true )
                case _                                        => assert( false )
              }
              */
              //val exnVar = ng.fresh( "vException" )
              assert( l( aux1 ).toUntypedString == exHypVar )
              val delL = l.delete( aux1 ).antecedent
              assert( r( newAux2 ).toUntypedString == forallHypVar )
              val delR = r.delete( newAux2 ).antecedent
              //val res = delL ++: delR ++: Sequent() :+ le"tryCatch ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              //if ( freeVariables( r( Suc( 0 ) ) ).contains( varR ) )
              //println( s"contains $varR" )
              //val res = delL ++: delR ++: Sequent() :+ le"(^$varR tryCatch($varR, ${r( Suc( 0 ) )}, handle($varR($varL), ${l( Suc( 0 ) )})))($exnVar)"
              val tmp1 = r( Suc( 0 ) )
              val tmp2 = l( Suc( 0 ) )
              val res = delL ++: delR ++: Sequent() :+ le"tryCatch(${forallEm1HypVarsPrime( All( x, -g ) )}, ${exEm1FormulasPrime( Ex( x, g ) )}, ${r( Suc( 0 ) )}, ${l( Suc( 0 ) )})"
              //println( s"tryCatch var: $varR, catch: ${varR( varL )}, tryCatch.ty: ${res( Suc( 0 ) ).ty}" )
              println( s"EM1: ${f}" )
              res

            case f if !containsQuantifierOnLogicalLevel( f ) =>
              val l = extractCases( leftSubProof, ng, exEm1HypVars, forallEm1HypVars )
              val r = extractCases( rightSubProof, ng, exEm1HypVars, forallEm1HypVars )
              val varL = l( aux1 ).asInstanceOf[Var]
              val varR = r( aux2 ).asInstanceOf[Var]
              /*
              varR.ty match {
                case TArr( varL.ty, TBase( "exn", varL.ty ) ) => assert( true )
                case _                                        => assert( false )
              }
              */
              //val exnVar = ng.fresh( "vException" )
              val delL = l.delete( aux1 ).antecedent
              val delR = r.delete( aux2 ).antecedent
              //val res = delL ++: delR ++: Sequent() :+ le"tryCatch ${Abs( varL, l( Suc( 0 ) ) )} ${Abs( varR, r( Suc( 0 ) ) )}"
              //if ( freeVariables( r( Suc( 0 ) ) ).contains( varR ) )
              //println( s"contains $varR" )
              //val res = delL ++: delR ++: Sequent() :+ le"(^$varR tryCatch($varR, ${r( Suc( 0 ) )}, handle($varR($varL), ${l( Suc( 0 ) )})))($exnVar)"
              val res = delL ++: delR ++: Sequent() :+ le"ite(${leftSubProof.endSequent( aux1 )}, ${l( Suc( 0 ) )}, ${r( Suc( 0 ) )})"
              //val res = delL ++: delR ++: Sequent() :+ le"tryCatch($varR, ${r( Suc( 0 ) )}, handle($varR($varL), ${l( Suc( 0 ) )}))"
              println( s"tryCatch var: $varR, catch: ${varR( varL )}, tryCatch.ty: ${res( Suc( 0 ) ).ty}" )
              //println( s"EM0: ${f}" )
              res

            case _ => throw new Exception( "EM_k for k > 1 not supported." )
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

  // computes the type of a potential m-realizer for the formula
  def flat( formula: Formula )( implicit ctx: Context ): Ty = formula match {
    case Bottom() => ty"exn" //TBase( "exn", ty"1" )
    case Top()    => ty"exn" ->: ty"exn" //TBase( "exn", ty"1" ) ->: TBase( "exn", ty"1" )
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
      ty"1" // ? e.ty ?
    case And( leftformula, rightformula ) =>
      TBase( "conj", flat( leftformula ), flat( rightformula ) )
    case Or( leftformula, rightformula ) =>
      TBase( "sum", flat( leftformula ), flat( rightformula ) )
    case Imp( leftformula, rightformula ) =>
      flat( leftformula ) ->: flat( rightformula )
    case Neg( subformula ) =>
      val typeParam = flat( subformula )
      flat( subformula ) ->: ty"exn" //TBase( "exn", typeParam )
    case Ex( variable, subformula ) =>
      TBase( "exconj", variable.ty, flat( subformula ) )
    case All( variable, subformula ) =>
      variable.ty ->: flat( subformula )
  }
  /**
   * removes all occurences of the empty program i : 1 from term, or is i : 1 itself,
   * except for match and inl and inr term: sometimes not possible to remove all occurences.
   */
  def remEmpProg( term: Expr )( implicit systemT: Context ): Expr = {

    val emptyType = ty"1"
    val empty = hoc"i:1"

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
        if ( remEmpProgType( typeparams( 0 ) ) == emptyType
          && remEmpProgType( typeparams( 1 ) ) == emptyType ) {
          empty
        } else {
          Const(
            "inl",
            TArr( remEmpProgType( termmtype ), TBase( "sum", remEmpProgTypes( typeparams ) ) ),
            remEmpProgTypes( params ) )( remEmpProg( termm ) )
        }

      case App( Const( "inr", TArr( termmtype, TBase( "sum", typeparams ) ), params ), termm ) =>
        if ( remEmpProgType( typeparams( 0 ) ) == emptyType
          && remEmpProgType( typeparams( 1 ) ) == emptyType ) {
          empty
        } else {
          Const(
            "inr",
            TArr( remEmpProgType( termmtype ), TBase( "sum", remEmpProgTypes( typeparams ) ) ),
            remEmpProgTypes( params ) )( remEmpProg( termm ) )
        }

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

      case App( App( Const( "bar", TArr( leftType, TArr( rightType, resultType ) ), params ), left ), right ) =>
        val leftR = remEmpProg( left )
        val rightR = remEmpProg( right )
        val ng = new NameGenerator( ( freeVariables( left ) ++ freeVariables( right ) ) map ( _.name ) )
        val leftRN = if ( remEmpProgType( params( 0 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), leftR ) else leftR
        val rightRN = if ( remEmpProgType( params( 1 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), rightR ) else rightR
        val resultTypeR = remEmpProgType( resultType )
        if ( resultTypeR == emptyType ) empty
        else Const(
          "bar",
          TArr( leftRN.ty, TArr( rightRN.ty, resultTypeR ) ),
          remEmpProgTypes( params ) )( leftRN, rightRN )

      case App( App( App( Const( "bar2", TArr( predType, TArr( leftType, TArr( rightType, resultType ) ) ), params ), pred ), left ), right ) =>
        val leftR = remEmpProg( left )
        val rightR = remEmpProg( right )
        val ng = new NameGenerator( ( freeVariables( left ) ++ freeVariables( right ) ) map ( _.name ) )
        val leftRN = if ( remEmpProgType( params( 1 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), leftR ) else leftR
        val rightRN = if ( remEmpProgType( params( 2 ) ) == emptyType ) Abs( Var( ng.fresh( "x" ), ty"1" ), rightR ) else rightR
        val resultTypeR = remEmpProgType( resultType )
        if ( resultTypeR == emptyType ) empty
        else Const(
          "bar2",
          TArr( predType, TArr( leftRN.ty, TArr( rightRN.ty, resultTypeR ) ) ),
          remEmpProgTypes( params ) )( remEmpProg( pred ), leftRN, rightRN )

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
        if ( leftsum == empty && rightsum == empty ) empty
        else TBase( "sum", leftsum, rightsum )

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
      case Abs( x, t )   => Abs( x, permuteEM( t ) )
      case App( t1, t2 ) => App( permuteEM( t1 ), permuteEM( t2 ) )
      case _             => println( s"Fallthrough: $term" ); term
    }
  }
}

class ClassicalExtractionCreationException( name: String, message: String ) extends Exception( s"Cannot create an m-realizer for $name: " + message )

