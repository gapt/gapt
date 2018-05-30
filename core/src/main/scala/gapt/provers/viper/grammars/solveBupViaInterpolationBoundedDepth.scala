package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.fol.folTermSize
import gapt.expr.hol.{ CNFp, instantiate, simplify, skolemize }
import gapt.proofs._
import gapt.provers.{ Prover, Session }
import gapt.provers.smtlib.{ SmtInterpol, Z3 }
import gapt.utils.Tree
import cats.implicits._
import gapt.expr.bdt.BDT
import gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }

import scala.collection.mutable

object solveBupViaInterpolationBoundedDepth {

  type PredVars = ( Var, Seq[Var] )

  def boundedUnfolding( bup: InductionBUP, i: Int ): Tree[( PredVars, Formula )] = {
    val nameGen = rename.awayFrom( containedNames( bup.formula ) )

    def u( nu: Var, gam: Seq[Var], i: Int ): Tree[( PredVars, Formula )] = {
      val bgth = mutable.Buffer[Formula]()
      val caseEqs = mutable.Buffer[Formula]()
      val children = mutable.Buffer[Tree[( PredVars, Formula )]]()
      for {
        cas <- bup.indCases
        if i > 0 || cas.indHyps.isEmpty
        nus = cas.nu.map( nameGen.fresh( _ ) )
      } {
        val subst = Substitution( ( cas.nu zip nus ) ++ ( bup.grammar.gamma zip gam ) )
        bgth += subst( cas.theoryFormulas.toNegConjunction )
        for {
          gamTerm <- cas.gammas
          gam_ = bup.grammar.gamma.map( nameGen.fresh( _ ) )
        } {
          for ( ( g, t ) <- gam_.zip( subst( gamTerm ) ) )
            bgth += Eq( g, t )
          for ( nu_ <- nus if nu_.ty == bup.grammar.indTy )
            children += u( nu_, gam_, i - 1 )
        }
        caseEqs += Eq( nu, cas.constructor( nus ) )
      }
      Tree( ( ( nu, gam ), And( Or( caseEqs ) +: bgth ) ), children.toVector )
    }

    {
      val bgth = mutable.Buffer[Formula]()
      val children = mutable.Buffer[Tree[( PredVars, Formula )]]()
      val nu_ = nameGen.fresh( bup.grammar.alpha )
      bgth += Eq( nu_, bup.grammar.alpha )
      bgth += bup.endCut.theoryFormulas.toNegConjunction
      bgth += -bup.goal
      for {
        gamTerm <- bup.endCut.gammas
        gam_ = bup.grammar.gamma.map( nameGen.fresh( _ ) )
      } {
        for ( ( g, t ) <- gam_.zip( gamTerm ) )
          bgth += Eq( g, t )
        children += u( nu_, gam_, i )
      }

      Tree( ( ( nu_, bup.grammar.gamma ), And( bgth ) ), children.toVector )
    }
  }

  def apply( bup: InductionBUP, i: Int = 0 ): Expr = {
    val tree = boundedUnfolding( bup, i )
    val Some( interpolants ) = SmtInterpol.getInterpolant( tree.map( _._2 ) )

    val nu = rename(
      ( bup.grammar.nus.values.toSeq.flatten :+ bup.grammar.alpha ).
        find( _.ty == bup.grammar.indTy ).head, bup.grammar.gamma.toSet + bup.grammar.alpha )
    val generalized =
      tree.zip( interpolants ).map {
        case ( ( ( nu_, gam ), _ ), interp ) =>
          TermReplacement( simplify( interp ), Map( nu_ -> nu ) ++ gam.zip( bup.grammar.gamma ) ): Formula
      }

    val solution = simplify( Or(
      generalized.zipWithDepth.postOrder.groupBy( _._2 ).
        values.map( _.map( _._1 ) ).map( And( _ ) ).
        filterNot( _ == Top() ) ) )
    TreeGrammarProver.logger.info( s"candidate solution: ${solution.toUntypedString}" )

    val sol = Abs.Block( bup.grammar.alpha +: nu +: bup.grammar.gamma, solution )

    val cond = skolemize( BetaReduction.betaNormalize( instantiate( bup.formula, sol ) ) )
    if ( SmtInterpol.isValid( cond ) )
      sol
    else
      apply( bup, i + 1 )
  }

}

object solveBupViaInterpolationConcreteTerms {

  def norm( t: Expr ): Expr =
    Substitution( for ( x <- freeVariables( t ) ) yield x -> Var( "x", x.ty ) )( t )

  type PredVars = ( Expr, Var, Seq[Var] )

  def boundedUnfolding( bup: InductionBUP, t: Expr ): Tree[( PredVars, Formula )] = {
    val nameGen = rename.awayFrom( containedNames( bup.formula ) )

    def u( nu: Var, gam: Seq[Var], t: Expr ): Tree[( PredVars, Formula )] = {
      val bgth = mutable.Buffer[Formula]()
      val caseEqs = mutable.Buffer[Formula]()
      val children = mutable.Buffer[Tree[( PredVars, Formula )]]()
      val Apps( ctr, args ) = t
      val Some( cas ) = bup.indCases.find( _.constructor == ctr )
      val nus = cas.nu.map( nameGen.fresh( _ ) )
      val subst = Substitution( ( cas.nu zip nus ) ++ ( bup.grammar.gamma zip gam ) )
      bgth += subst( cas.theoryFormulas.toNegConjunction )
      for {
        gamTerm <- cas.gammas
        gam_ = bup.grammar.gamma.map( nameGen.fresh( _ ) )
      } {
        for ( ( g, t ) <- gam_.zip( subst( gamTerm ) ) )
          bgth += Eq( g, t )
        for ( ( nu_, a ) <- nus zip args if nu_.ty == bup.grammar.indTy )
          children += u( nu_, gam_, a )
      }
      caseEqs += Eq( nu, cas.constructor( nus ) )
      Tree( ( ( norm( t ), nu, gam ), And( Or( caseEqs ) +: bgth ) ), children.toVector )
    }

    {
      val bgth = mutable.Buffer[Formula]()
      val children = mutable.Buffer[Tree[( PredVars, Formula )]]()
      val nu_ = nameGen.fresh(
        ( bup.grammar.nus.values.toSeq.flatten :+ bup.grammar.alpha ).
          find( _.ty == bup.grammar.indTy ).head )
      bgth += Eq( nu_, bup.grammar.alpha )
      bgth += bup.endCut.theoryFormulas.toNegConjunction
      bgth += -bup.goal
      for {
        gamTerm <- bup.endCut.gammas
        gam_ = bup.grammar.gamma.map( nameGen.fresh( _ ) )
      } {
        for ( ( g, t ) <- gam_.zip( gamTerm ) )
          bgth += Eq( g, t )
        children += u( nu_, gam_, t )
      }

      Tree( ( ( norm( t ), nu_, bup.grammar.gamma ), And( bgth ) ), children.toVector )
    }
  }

  def improve( context: Formula, start: Formula, instances: Set[Substitution], prover: Prover,
               hasEquality: Boolean, forgetOne: Boolean ): Formula = {
    import gapt.provers.Session._
    val names = containedNames( instances ) ++ containedNames( start ) ++ containedNames( context )
    val nameGen = rename.awayFrom( names )
    val grounding = Substitution( for ( v <- freeVariables( start & context ) ++ instances.flatMap( _.range ) )
      yield v -> Const( nameGen.fresh( v.name ), v.ty ) )
    val groundInstances = instances.map( grounding.compose )

    def checkSolution( cnf: Set[HOLClause] ): Session[Option[Formula]] = {
      val clauses = for ( inst <- groundInstances; clause <- cnf ) yield inst( clause.toDisjunction )

      withScope( assert( clauses.toList ) >> checkUnsat ).flatMap { isSolOrUnknown =>
        val isSol = isSolOrUnknown.getOrElse( false )

        if ( isSol ) {
          val next =
            ( if ( forgetOne ) cnf.toList.map( cnf - _ ) else Nil ) ++
              forgetfulPropResolve( cnf ).toList ++
              ( if ( hasEquality ) forgetfulPropParam( cnf ).toList else Nil )

          def findFirst( next: List[Set[HOLClause]] ): Session[Option[Formula]] =
            next match {
              case n :: ns =>
                checkSolution( n ).flatMap {
                  case Some( sol ) => Session.pure( Some( sol ) )
                  case None =>
                    findFirst( ns )
                }
              case Nil =>
                Session.pure( Some( And( cnf.map( _.toFormula ) ) ) )
            }

          findFirst( next )
        } else {
          Session.pure( None )
        }
      }
    }

    prover.runSession {
      declareSymbolsIn( names ++ containedNames( grounding ) ) >>
        assert( grounding( -context ) ) >>
        checkSolution( CNFp( start ).map { _.distinct.sortBy { _.hashCode } } )
    }.get
  }

  def improveAt( interps: Map[Expr, Formula], t: Expr, bup: InductionBUP, nu: Var ): Formula = {
    val nameGen = rename.awayFrom( containedNames( bup.formula ) ++ containedNames( interps.values.toSeq ) + nu )

    val insts = mutable.Buffer[List[Var]]()
    val contexts = mutable.Buffer[Formula]()

    def getInsts( args: Seq[List[Expr]] ): Formula = {
      while ( insts.size < args.size )
        insts += ( nu +: bup.grammar.gamma ).map( nameGen.fresh( _ ) )

      And( for ( ( is, as ) <- insts zip args; ( i, a ) <- is zip as ) yield i === a )
    }

    contexts +=
      ( getInsts( bup.endCut.gammas.map( bup.grammar.alpha +: _ ) ) &
        bup.endCut.theoryFormulas.toNegConjunction ) --> bup.goal

    for {
      ( par @ Apps( ctr: Const, parArgs ), f ) <- interps
      if parArgs contains t
      cas <- bup.indCases if cas.constructor == ctr
    } contexts +=
      ( cas.theoryFormulas.toNegConjunction & And(
        for ( ( nui, t_ ) <- cas.nu zip parArgs if nui.ty == bup.grammar.indTy )
          yield if ( t_ == t )
          getInsts( cas.gammas.map( nui +: _ ) )
        else
          And( for ( gam <- cas.gammas )
            yield Substitution( ( nu -> nui ) +: ( bup.grammar.gamma zip gam ) )( interps( t_ ) ) ) ) ) -->
        Substitution( nu -> ctr( cas.nu ) )( f )

    improve( And( contexts ), interps( t ),
      Set() ++ ( for ( is <- insts ) yield Substitution( ( nu +: bup.grammar.gamma ) zip is ) ),
      Z3, hasEquality = true, forgetOne = true )
  }

  def improve( interps: Map[Expr, Formula], bup: InductionBUP, nu: Var ): Map[Expr, Formula] =
    interps.keys.toSeq.sortBy( -folTermSize( _ ) ).foldLeft( interps )( ( interps, t ) =>
      interps.updated( t, improveAt( interps, t, bup, nu ) ) )

  def apply( bup: InductionBUP, ts: Stream[Expr] ): Expr =
    apply( bup, ts, Map(), rename(
      ( bup.grammar.nus.values.toSeq.flatten :+ bup.grammar.alpha ).
        find( _.ty == bup.grammar.indTy ).head, bup.grammar.gamma.toSet + bup.grammar.alpha ) )

  def apply( bup: InductionBUP, ts: Stream[Expr], prev: Map[Expr, Formula], nu: Var ): Expr = {
    val tree = boundedUnfolding( bup, ts.head )
    val Some( interpolants ) = SmtInterpol.getInterpolant( tree.map( _._2 ) ).
      map( _.map( simplify( _ ) ) )

    val generalized =
      tree.zip( interpolants ).map {
        case ( ( ( t, nu_, gam ), _ ), interp ) =>
          t -> ( TermReplacement( simplify( interp ), Map( nu_ -> nu ) ++ gam.zip( bup.grammar.gamma ) ): Formula )
      }

    val grouped = Map() ++
      generalized.postOrder.dropRight( 1 ).groupBy( _._1 ).
      mapValues( fs => And( fs.map( _._2 ) ) )

    val groupedAndPrev =
      ( grouped.keySet ++ prev.keySet ).
        map( k => k -> simplify( grouped.getOrElse( k, Top() ) & prev.getOrElse( k, Top() ) ) ).
        toMap

    // val improved = groupedAndPrev
    // val improved = improve( groupedAndPrev, bup, nu )
    val improved = groupedAndPrev.map { case ( k, f ) => k -> BDT( f ).simpEq.toFormula }

    val solution = simplify( BDT( Or( improved.values.filterNot( _ == Top() ) ) ).simpEq.toFormula )
    TreeGrammarProver.logger.info( s"candidate solution: ${solution.toUntypedString}" )

    val sol = Abs.Block( bup.grammar.alpha +: nu +: bup.grammar.gamma, solution )

    val cond = skolemize( BetaReduction.betaNormalize( instantiate( bup.formula, sol ) ) )
    if ( SmtInterpol.isValid( cond ) )
      sol
    else
      apply( bup, ts.tail, improved, nu )
  }

}
