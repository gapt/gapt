package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs._

object eliminateSplitting {
  def apply( p: ResolutionProof ): ResolutionProof = p match {
    case Splitting( splittingClause, part1, part2, case1, case2 ) =>
      justOne( Splitting( splittingClause, part1, part2, apply( case1 ), apply( case2 ) ) )
    case _ => p
  }

  def justOne( split: Splitting ): ResolutionProof = {
    val Splitting( splittingClause, part1, part2, subProof1, subProof2 ) = split

    val nameGen = rename.awayFrom(
      splittingClause.subProofs union subProof1.subProofs union subProof2.subProofs
        collect { case Instance( _, subst ) => subst.domain } flatten
    )

    val projections1 = for ( ( a, i ) <- part1.zipWithIndex if freeVariables( a ).isEmpty )
      yield mapInputClauses.withOccConn( subProof1, factorEverything = true ) {
      case clause if clause == part1 =>
        TautologyClause( a ) -> OccConnector( a +: Clause() :+ a, clause,
          if ( i isSuc ) Seq() +: Sequent() :+ Seq( i )
          else Seq( i ) +: Sequent() :+ Seq() )
      case clause => InputClause( clause ) -> OccConnector( clause )
    }

    val part2renaming = freeVariables( part2 ).map { v => v -> nameGen.fresh( v ) }
    val renamedSplittingClause = Instance( splittingClause, Substitution( part2renaming ) )
    val renamedPart1OccConn = OccConnector( part1, Substitution( part2renaming )( splittingClause.conclusion ).map { _.asInstanceOf[HOLAtom] },
      for ( ( a, i ) <- part1.zipWithIndex ) yield Seq( splittingClause.conclusion.indexOfPol( a, i.isSuc ) ) )
    val renamedDerivationOfPart2 = mapInputClauses.withOccConn( subProof1, factorEverything = true ) { clause =>
      if ( clause == part1 ) {
        renamedSplittingClause -> renamedPart1OccConn.inv
      } else {
        InputClause( clause ) -> OccConnector( clause )
      }
    }
    val derivationOfPart2 = Instance( renamedDerivationOfPart2, Substitution( part2renaming.map { _.swap } ) )
    require( derivationOfPart2.conclusion isSubMultisetOf part2 )

    val finalProof = mapInputClauses( subProof2, factorEarly = true ) { clause =>
      if ( clause == part2 ) {
        derivationOfPart2
      } else {
        projections1.find( _.conclusion isSubsetOf clause ).map( projections1( _ ) ).getOrElse( InputClause( clause ) )
      }
    }
    require( finalProof.conclusion.isEmpty )

    finalProof
  }
}
