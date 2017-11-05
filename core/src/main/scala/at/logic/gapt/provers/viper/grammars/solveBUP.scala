package at.logic.gapt.provers.viper.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.{ RecSchemTemplate, RecursionScheme, Rule }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.escargot.impl.getFOPositions

import scala.collection.mutable

object hSolveQBUP {
  def findConseq( start: Formula, conds: Seq[( Set[Substitution], Formula )],
                  prover: Prover, equations: Seq[Formula] ): Set[Formula] = {
    val isSolution = mutable.Map[Set[HOLClause], Boolean]()
    def checkSol( cnf: Set[HOLClause] ) = isSolution.getOrElseUpdate( cnf, {
      val cnfForm = And( cnf.map( _.toDisjunction ) )
      val cond = And( for ( ( substs, f ) <- conds ) yield And( substs.map( _( cnfForm ) ) ) --> f )
      prover.isValid( cond )
    } )

    def normalize( clause: HOLClause ): HOLClause =
      clause.distinct.sortBy( _.hashCode )

    type Node = ( Set[HOLClause], Seq[Formula] )
    val didInferences = mutable.Set[Node]()
    def forgetfulInferences( node: Node ): Unit = {
      if ( !didInferences( node ) ) {
        val ( cnf, equations ) = node
        if ( checkSol( cnf ) ) {
          for ( cnf_ <- forgetfulPropResolve( cnf ) ) forgetfulInferences( ( cnf_, equations ) )
          for ( cnf_ <- forgetfulPropParam( cnf ) ) forgetfulInferences( ( cnf_, equations ) )
          for {
            ( Eq( lhs0, rhs0 ), i ) <- equations.zipWithIndex
            ltr <- Seq( true, false )
            ( lhs, rhs ) = if ( ltr ) ( lhs0, rhs0 ) else ( rhs0, lhs0 )
            cls <- cnf
            ( a, j ) <- cls.zipWithIndex
            ( e, ps ) <- getFOPositions( a )
            subst <- syntacticMatching( lhs, e )
            rhs_ = subst( rhs )
            p <- ps
            a_ = a.replace( p, rhs_ ).asInstanceOf[Atom]
          } forgetfulInferences( ( cnf - cls + normalize( cls.replaceAt( j, a_ ) ),
            for ( ( e, i_ ) <- equations.zipWithIndex if i_ != i ) yield e ) )
        }
        didInferences += node
      }
    }
    forgetfulInferences( CNFp( start ).map( normalize ) -> equations )

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
        throw new IllegalArgumentException( s"Cannot backchain $xInst in:\n\n${qbupSequents.mkString( "\n\n" )}" ) )

    mkCanSol( xInst )
  }

  def apply( qbupMatrix: Formula, xInst: Formula, prover: Prover, equations: Seq[Formula] = Seq() ): Option[Expr] = {
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

    val conseqs = findConseq( start, searchConds, prover, equations )

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
