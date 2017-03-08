package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.{ RecSchemTemplate, RecursionScheme, Rule }
import at.logic.gapt.proofs.lk.skolemize
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }
import at.logic.gapt.provers.Prover

import scala.collection.mutable

case class MaxSatRecSchemFinder(
    paramTys:         Seq[Ty],
    pi1QTys:          Seq[TBase],
    instanceType:     Ty,
    grammarWeighting: Rule => Int,
    viaInst:          Boolean,
    context:          Context
) extends InductiveGrammarFindingMethod {
  implicit def ctx = context

  val vs = for ( ( t, i ) <- paramTys.zipWithIndex ) yield Var( s"z$i", t )
  val A = Const( "A", FunctionType( instanceType, paramTys ) )
  val template = simplePi1RecSchemTempl( A( vs ), pi1QTys )

  def findRS( taggedLanguage: Set[( Seq[Expr], Expr )] ): RecursionScheme = {
    val targets = for ( ( ts, r ) <- taggedLanguage ) yield A( ts ) -> r
    if ( viaInst )
      template.findMinimalCoverViaInst( targets, weight = grammarWeighting )
    else
      template.findMinimalCover( targets, weight = grammarWeighting )
  }
}

object simplePi1RecSchemTempl {
  def apply( startSymbol: Expr, pi1QTys: Seq[TBase] )( implicit ctx: Context ): RecSchemTemplate = {
    val nameGen = rename.awayFrom( ctx.constants )

    val Apps( startSymbolNT: Const, startSymbolArgs ) = startSymbol
    val FunctionType( instTT, startSymbolArgTys ) = startSymbolNT.ty
    // TODO: handle strong quantifiers in conclusion correctly
    val startSymbolArgs2 = for ( ( t, i ) <- startSymbolArgTys.zipWithIndex ) yield Var( s"x_$i", t )

    val indLemmaNT = Const( nameGen fresh "B", FunctionType( instTT, startSymbolArgTys ++ startSymbolArgTys ++ pi1QTys ) )

    val lhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w_$i", t )
    val rhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"v_$i", t )

    val indLemmaRules = startSymbolArgTys.zipWithIndex.flatMap {
      case ( indLemmaArgTy, indLemmaArgIdx ) =>
        val indTy = indLemmaArgTy.asInstanceOf[TBase]
        ctx.getConstructors( indTy ) match {
          case None => Seq()
          case Some( ctrs ) =>
            ctrs flatMap { ctr =>
              val FunctionType( _, ctrArgTys ) = ctr.ty
              val ctrArgs = for ( ( t, i ) <- ctrArgTys.zipWithIndex ) yield Var( s"x_${indLemmaArgIdx}_$i", t )
              val lhs = indLemmaNT( startSymbolArgs )( startSymbolArgs2.take( indLemmaArgIdx ) )( ctr( ctrArgs: _* ) )( startSymbolArgs2.drop( indLemmaArgIdx + 1 ) )( lhsPi1QArgs )
              val recRules = ctrArgTys.zipWithIndex.filter { _._1 == indTy } map {
                case ( ctrArgTy, ctrArgIdx ) =>
                  lhs -> indLemmaNT( startSymbolArgs )( startSymbolArgs2.take( indLemmaArgIdx ) )( ctrArgs( ctrArgIdx ) )( startSymbolArgs2.drop( indLemmaArgIdx + 1 ) )( rhsPi1QArgs )
              }
              recRules :+ ( lhs -> Var( "u", instTT ) )
            }
        }
    }

    RecSchemTemplate(
      startSymbolNT,
      indLemmaRules.toSet
        + ( startSymbolNT( startSymbolArgs: _* ) -> indLemmaNT( startSymbolArgs: _* )( startSymbolArgs: _* )( rhsPi1QArgs: _* ) )
        + ( startSymbolNT( startSymbolArgs: _* ) -> Var( "u", instTT ) )
    //        + ( indLemmaNT( startSymbolArgs: _* )( lhsPi1QArgs: _* ) -> Var( "u", instTT ) )
    )
  }
}

object canonicalRsLHS {
  def apply( recSchem: RecursionScheme )( implicit ctx: Context ): Set[Expr] =
    recSchem.nonTerminals flatMap { nt =>
      val FunctionType( To, argTypes ) = nt.ty
      val args = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x$i", t )
      recSchem.rulesFrom( nt ).flatMap {
        case Rule( Apps( _, as ), _ ) => as.zipWithIndex.filterNot { _._1.isInstanceOf[Var] }.map { _._2 }
      }.toSeq match {
        case Seq() => Some( nt( args: _* ) )
        case idcs =>
          val newArgs = for ( ( _: TBase, idx ) <- argTypes.zipWithIndex ) yield if ( !idcs.contains( idx ) ) List( args( idx ) )
          else {
            val indTy = argTypes( idx ).asInstanceOf[TBase]
            val Some( ctrs ) = ctx.getConstructors( indTy )
            for {
              ctr <- ctrs.toList
              FunctionType( _, ctrArgTys ) = ctr.ty
            } yield ctr(
              ( for ( ( t, i ) <- ctrArgTys.zipWithIndex ) yield Var( s"x${idx}_$i", t ) ): _*
            )
          }
          import cats.syntax.traverse._, cats.instances.list._
          newArgs.traverse( identity ).map( nt( _: _* ) )
      }
    }
}

object homogenizeRS {
  def apply( recSchem: RecursionScheme )( implicit ctx: Context ): RecursionScheme = {
    val lhss = canonicalRsLHS( recSchem )
    val rules =
      for {
        lhs <- lhss
        r @ Rule( lhs_, rhs ) <- recSchem.rules
        subst <- syntacticMatching( lhs_, lhs )
      } yield subst( r )
    val terminalRHSs = rules collect { case Rule( _, rhs @ Apps( hd: Const, _ ) ) if !recSchem.nonTerminals( hd ) => rhs }
    val extraRules = for ( lhs <- lhss; rhs <- terminalRHSs if freeVariables( rhs ) subsetOf freeVariables( lhs ) ) yield Rule( lhs, rhs )
    recSchem.copy( rules = rules ++ extraRules )
  }
}

object qbupForRecSchem {
  def apply( recSchem: RecursionScheme, conj: Formula )( implicit ctx: Context ): Formula = {
    def convert( term: Expr ): Formula = term match {
      case Apps( ax, args ) if ax == recSchem.startSymbol => instantiate( conj, args )
      case Apps( nt @ Const( name, ty ), args ) if recSchem.nonTerminals contains nt =>
        Atom( Var( s"X_$name", ty )( args: _* ) )
      case formula: Formula => formula
    }

    val lhss = canonicalRsLHS( recSchem )

    existentialClosure( And( for ( lhs <- lhss ) yield All.Block(
      freeVariables( lhs ) toSeq,
      formulaToSequent.pos( And( for {
        Rule( lhs_, rhs ) <- recSchem.rules
        subst <- syntacticMatching( lhs_, lhs )
      } yield convert( subst( rhs ) ) )
        --> convert( lhs ) ).toImplication
    ) ) )
  }
}

object hSolveQBUP {
  def findConseq( start: Formula, conds: Seq[( Set[Substitution], Formula )],
                  prover: Prover ): Set[Formula] = {
    val isSolution = mutable.Map[Set[HOLClause], Boolean]()
    def checkSol( cnf: Set[HOLClause] ) = isSolution.getOrElseUpdate( cnf, {
      val cnfForm = And( cnf.map( _.toDisjunction ) )
      val cond = And( for ( ( substs, f ) <- conds ) yield And( substs.map( _( cnfForm ) ) ) --> f )
      prover.isValid( cond )
    } )

    val didInferences = mutable.Set[Set[HOLClause]]()
    def forgetfulInferences( cnf: Set[HOLClause] ): Unit =
      if ( !didInferences( cnf ) ) {
        if ( checkSol( cnf ) ) {
          forgetfulPropResolve( cnf ) foreach forgetfulInferences
          forgetfulPropParam( cnf ) foreach forgetfulInferences
        }
        didInferences += cnf
      }
    forgetfulInferences( CNFp( start ).map { _.distinct.sortBy { _.hashCode } } )

    val didForget = mutable.Set[Set[HOLClause]]()
    def forgetClauses( cnf: Set[HOLClause] ): Unit =
      if ( !didForget( cnf ) ) {
        if ( checkSol( cnf ) ) for ( c <- cnf ) forgetClauses( cnf - c )
        didForget += cnf
      }
    for ( ( cnf, true ) <- isSolution.toSeq ) forgetClauses( cnf )

    isSolution collect { case ( sol, true ) => simplify( And( sol map { _.toImplication } ) ) } toSet
  }

  def getSequents( qbupMatrix: Formula, x: Var ): Seq[HOLSequent] = {
    val qbupSequents = And.nAry.unapply( qbupMatrix ).get.
      map { case All.Block( _, matrix ) => formulaToSequent.pos( matrix ) }
    for ( seq <- qbupSequents; formula <- seq )
      formula match {
        case Apps( `x`, _ ) =>
        case other =>
          require( !containsQuantifier( other ) )
          require( !freeVariables( other ).contains( x ) )
      }
    qbupSequents
  }

  def canonicalSolution( qbupMatrix: Formula, xInst: Formula ): Formula = {
    val Apps( x: Var, xInstArgs ) = xInst
    val qbupSequents = getSequents( qbupMatrix, x )

    val posOccurs = for {
      seq <- qbupSequents
      ( occ @ Apps( `x`, _ ), idx ) <- seq.zipWithIndex.succedent
    } yield occ -> seq.delete( idx )
    def mkCanSol( xInst: Formula ): Formula =
      ( for {
        ( occ, seq ) <- posOccurs.view
        subst <- syntacticMatching( occ, xInst )
      } yield subst( seq ).map {
        case nextOcc @ Apps( `x`, _ ) => mkCanSol( nextOcc )
        case notX                     => notX
      }.toNegConjunction ).headOption.getOrElse(
        throw new IllegalArgumentException( s"Cannot backchain $xInst in:\n\n${qbupSequents.mkString( "\n\n" )}" )
      )

    mkCanSol( xInst )
  }

  def apply( qbupMatrix: Formula, xInst: Formula, prover: Prover ): Option[Expr] = {
    val Apps( x: Var, xInstArgs ) = xInst
    val qbupSequents = getSequents( qbupMatrix, x )

    val start = canonicalSolution( qbupMatrix, xInst )

    def mkSearchCond( substs0: Set[Substitution], seq0: HOLSequent ): Option[( Set[Substitution], Formula )] = {
      val renaming = Substitution( rename( freeVariables( seq0 ) - x, freeVariables( xInst ) ) )
      val seq = renaming( seq0 )
      val substs = substs0.map( renaming.compose )

      seq.indicesWhere { case Apps( hd, _ ) => hd == x } match {
        case occs if occs.exists( _.isSuc ) => None
        case Seq()                          => Some( substs -> seq.toImplication )
        case Seq( occ, _* ) =>
          syntacticMGU( xInst, seq( occ ) ).flatMap( subst =>
            mkSearchCond( substs.map( subst.compose ) + subst, subst( seq.delete( occ ) ) ) )
      }
    }

    val searchConds = qbupSequents.flatMap( mkSearchCond( Set(), _ ) )

    val conseqs = findConseq( start, searchConds, prover )

    val xGenArgs = for ( ( a, i ) <- xInstArgs.zipWithIndex ) yield Var( s"x$i", a.ty )
    val xGen = x( xGenArgs: _* )
    val Some( matching ) = syntacticMatching( xGen, xInst )
    def checkSolutionMatrix( matrix: Formula ) = {
      val sol = Abs( xGenArgs, matrix )
      if ( prover.isValid( skolemize( BetaReduction.betaNormalize( Substitution( x -> sol )( qbupMatrix ) ) ) ) )
        Some( sol )
      else None
    }
    // try uniform replacements first
    conseqs.toSeq.sortBy( expressionSize( _ ) ).view.flatMap { conseq =>
      val genConseq = TermReplacement( conseq, matching.map.map( _.swap ) )
      checkSolutionMatrix( genConseq )
    }.headOption.
      // now try replacing each occurrence
      orElse( conseqs.toSeq.sortBy( c => matching.map.values.flatMap( c.find ).size ).view.flatMap { conseq =>
        def generalize( genConseq: Expr, poss: List[HOLPosition] ): Option[Expr] = poss match {
          case Nil =>
            checkSolutionMatrix( genConseq.asInstanceOf[Formula] )
          case pos :: poss_ =>
            genConseq.get( pos ) match {
              case None =>
                generalize( genConseq, poss_ )
              case Some( termToGen ) =>
                matching.map.filter( _._2 == termToGen ).keys.view.flatMap { repl =>
                  generalize( genConseq.replace( pos, repl ), poss_ )
                }.headOption.orElse( generalize( genConseq, poss_ ) )
            }
        }
        generalize( conseq, matching.map.values.flatMap( conseq.find ).toList.sortBy( _.list.size ) )
      }.headOption )
  }
}
