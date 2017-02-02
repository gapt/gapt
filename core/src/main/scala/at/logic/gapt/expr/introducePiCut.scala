package at.logic.gapt.expr

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.Sequent

/**
 * Created by root on 26.01.17.
 */
class pi2SeHs(
    val reducedRepresentation:         Sequent[FOLFormula], // F[x\U_1] |- G[y\U_2]
    val universalEigenvariable:        FOLVar, // alpha
    val existentialEigenvariables:     List[FOLVar], // beta_1,...,beta_m
    val substitutionsForAlpha:         List[LambdaExpression], // r_1,...,r_m
    val substitutionsForBetaWithAlpha: List[LambdaExpression] // t_1(alpha),...,t_p(alpha)
) {

  require( existentialEigenvariables.length == substitutionsForAlpha.length )

  val multiplicityOfAlpha: Int = substitutionsForAlpha.length // m
  val multiplicityOfBeta: Int = substitutionsForBetaWithAlpha.length // p
  var balancedSolution: Option[FOLFormula] = None
  var noSolutionHasBeenFound: Boolean = true

  // (alpha,r_1),...,(alpha,r_m)
  //////////////////////////////
  def substitutionPairsAlpha(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsAlpha = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForAlpha.foreach( instance => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( universalEigenvariable, instance )
      substitutionPairsAlpha += buffer
    } )
    substitutionPairsAlpha.toSet
  }

  // (beta_i,t_1(alpha)),...,(beta_i,t_p(alpha))
  //////////////////////////////////////////////
  def substitutionPairsBetaI( index: Int ): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBetaI = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      val buffer: ( LambdaExpression, LambdaExpression ) = ( existentialEigenvariables( index - 1 ), instanceB )
      substitutionPairsBetaI += buffer
    } )
    substitutionPairsBetaI.toSet
  }

  // (beta_1,t_1(alpha)),...,(beta_1,t_p(alpha)),
  //                     ...                    ,
  // (beta_m,t_1(alpha)),...,(beta_m,t_p(alpha))
  ///////////////////////////////////////////////
  def substitutionPairsBeta(): Set[( LambdaExpression, LambdaExpression )] = {

    val substitutionPairsBeta = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    for ( index <- 1 to multiplicityOfAlpha ) {
      substitutionPairsBeta ++= substitutionPairsBetaI( multiplicityOfAlpha - index + 1 )
    }
    substitutionPairsBeta.toSet
  }

  // (alpha->r_1),...,(alpha->r_m)
  ////////////////////////////////
  def substitutionsAlpha(): List[Substitution] = {

    val substitutionsAlpha = scala.collection.mutable.ListBuffer[Substitution]()
    substitutionsForAlpha.foreach( instanceA => {
      substitutionsAlpha += Substitution( universalEigenvariable, instanceA )
    } )
    substitutionsAlpha.toList
  }

  // (beta_i->t_1(r_i)),...,(beta_i->t_p(r_i))
  ////////////////////////////////////////////
  def substitutionsBetaI( index: Int ): List[Substitution] = {

    val substitutionsBeta = scala.collection.mutable.ListBuffer[Substitution]()
    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) ) // (alpha->r_i)
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      substitutionsBeta += Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) )
    } )
    substitutionsBeta.toList
  }

  private def substituteRightSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.succedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = resultingSequent :+ formula
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = resultingSequent :+ subs( formula )
        } )
      }
    } )

    resultingSequent
  }

  private def substituteLeftSideOnce( sequent: Sequent[HOLFormula], index: Int ): Sequent[HOLFormula] = {

    var resultingSequent: Sequent[HOLFormula] = Sequent()

    sequent.antecedent.foreach( formula => {
      formula.find( existentialEigenvariables( index - 1 ) ) match {
        case List() => resultingSequent = formula +: resultingSequent
        case _ => substitutionsBetaI( index ).foreach( subs => {
          resultingSequent = subs( formula ) +: resultingSequent
        } )
      }
    } )

    resultingSequent
  }

  // F[x\T_1] |- G[y\T_2]
  ///////////////////////
  def herbrandSequent(): Sequent[HOLFormula] = {

    var herbrandSequent: Sequent[HOLFormula] = Sequent() :++ reducedRepresentation.succedent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteRightSideOnce( herbrandSequent, multiplicityOfAlpha - indexM )
    }

    reducedRepresentation.antecedent.foreach( formula => {
      substitutionsForAlpha.foreach( instanceA => {
        val subs: Substitution = Substitution( universalEigenvariable, instanceA )
        herbrandSequent = subs( formula ) +: herbrandSequent
      } )
    } )

    val sequent: Sequent[HOLFormula] = herbrandSequent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteLeftSideOnce( herbrandSequent.antecedent ++: Sequent(), multiplicityOfAlpha - indexM ) :++ sequent.succedent
    }

    herbrandSequent
  }

  // The reduced representation as a formula
  //////////////////////////////////////////
  val reducedRepresentationToFormula: FOLFormula = reducedRepresentation.toImplication

}

class LeafIndex(
  var oneToMList: Set[Int],
  var oneToPList: Set[Int]
) {}

class LiteralWithIndexLists(
    val literal:       FOLFormula,
    val leafIndexList: List[LeafIndex],
    val numberOfDNTAs: Int
) {
  // require( numberOfDNTAs == leafIndexList.length )
}

class ClauseWithIndexLists(
    val literals: List[LiteralWithIndexLists]
) {

  // require( literals.tail.forall( _.numberOfDNTAs == literals.head.numberOfDNTAs ) )

  def numberOfDNTAs: Int = this.literals.head.numberOfDNTAs

  def leafIndexList: List[LeafIndex] = {

    val leafIndexListBuffer: List[LeafIndex] = this.literals.head.leafIndexList
    this.literals.tail.foreach( literal => for ( leafNumber <- 0 until literal.numberOfDNTAs ) {
      leafIndexListBuffer( leafNumber ).oneToPList = leafIndexListBuffer( leafNumber ).oneToPList.intersect( literal.leafIndexList( leafNumber ).oneToPList )
      leafIndexListBuffer( leafNumber ).oneToMList = leafIndexListBuffer( leafNumber ).oneToMList.union( literal.leafIndexList( leafNumber ).oneToMList )
    } )
    leafIndexListBuffer
  }

  def isAllowedAtLeastAsSubformula: Boolean = {

    var bool: Boolean = false
    this.leafIndexList.foreach( leafNumber => {
      if ( leafNumber.oneToPList.nonEmpty ) {
        bool = true
      }
    } )
    bool
  }

  def isAllowed: Boolean = {

    var bool: Boolean = false
    if ( this.isAllowedAtLeastAsSubformula ) {
      bool = true
      this.leafIndexList.foreach( leafNumber => {
        if ( leafNumber.oneToMList.isEmpty ) {
          bool = false
        }
      } )
    }
    bool
  }

  def formula: FOLFormula = {

    var formulaBuffer: FOLFormula = literals.head.literal
    literals.tail.foreach( literal => formulaBuffer = And( formulaBuffer, literal.literal ) )
    formulaBuffer
  }

}

class ClausesWithIndexLists(
    val clauses: List[ClauseWithIndexLists]
) {

  private def leafIndexList: List[LeafIndex] = {

    var emptyList: Boolean = false
    val leafIndexListBuffer: List[LeafIndex] = this.clauses.head.leafIndexList
    this.clauses.tail.foreach( clause => for ( leafNumber <- 0 until clause.numberOfDNTAs; if !emptyList ) {
      leafIndexListBuffer( leafNumber ).oneToPList = leafIndexListBuffer( leafNumber ).oneToPList.union( clause.leafIndexList( leafNumber ).oneToPList )
      leafIndexListBuffer( leafNumber ).oneToMList = leafIndexListBuffer( leafNumber ).oneToMList.intersect( clause.leafIndexList( leafNumber ).oneToMList )
      if ( leafIndexListBuffer( leafNumber ).oneToMList.isEmpty ) {
        emptyList = true
      }
    } )
    if ( emptyList ) {
      leafIndexListBuffer( 0 ).oneToPList = Set()
    }
    leafIndexListBuffer
  }

  def isSolution: Boolean = {

    var bool: Boolean = true
    this.leafIndexList.forall( leafNumber => {
      if ( leafNumber.oneToPList.isEmpty ) {
        bool = false
      } else if ( leafNumber.oneToMList.isEmpty ) {
        bool = false
      }
      bool
    } )
  }

  def formula: FOLFormula = {

    var formulaBuffer: FOLFormula = this.clauses.head.formula
    this.clauses.tail.foreach( clause => formulaBuffer = Or( formulaBuffer, clause.formula ) )
    formulaBuffer
  }

}

object introducePi2Cut {

  def apply(
    seHs:                      pi2SeHs,
    nameOfExistentialVariable: FOLVar  = fov"yCut",
    nameOfUniversalVariable:   FOLVar  = fov"xCut"
  ): Option[FOLFormula] = {

    val nameOfExistentialVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfExistentialVariable )
    val nameOfUniversalVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfUniversalVariable )

    val literals = scala.collection.mutable.Set[FOLFormula]()
    val DNTA = scala.collection.mutable.Set[Sequent[FOLFormula]]()

    CNFp( seHs.reducedRepresentationToFormula ).foreach( clause => if ( !clause.isTaut ) {
      var NTAClause: Sequent[FOLFormula] = clause
      for ( literal <- clause.succedent ) {
        NTAClause = Neg( literal ) +: NTAClause
      }
      NTAClause = NTAClause.antecedent ++: Sequent()
      DNTA += NTAClause // define for fol and hol sequents
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )

    val DNTAList = DNTA.toList

    val unifiedLiterals: Set[FOLFormula] = gStarUnify(
      literals.toSet,
      seHs.substitutionPairsAlpha(),
      seHs.substitutionPairsBeta(),
      seHs.universalEigenvariable,
      seHs.existentialEigenvariables,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    val literalsWithIndexLists: Set[LiteralWithIndexLists] = computeTheIndexListsForTheLiterals(
      unifiedLiterals,
      DNTAList,
      seHs,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    for ( literal <- literalsWithIndexLists ) {
      println( "literal" )
      println( literal.literal )
      println( "literalAsClauseProps" )
      println( "isAllowed" )
      println( new ClauseWithIndexLists( List( literal ) ).isAllowed )
      println( "isAllowedAtLeastAs..." )
      println( new ClauseWithIndexLists( List( literal ) ).isAllowedAtLeastAsSubformula )
      println( "IndexLists" )
      for ( leafNumber <- literal.leafIndexList ) {
        if ( leafNumber.oneToPList.nonEmpty && leafNumber.oneToMList.nonEmpty ) {
          println( "PList" )
          println( leafNumber.oneToPList )
          println( "MList" )
          println( leafNumber.oneToMList )
        }
      }
      println( literal.numberOfDNTAs )
    }

    if ( literalsWithIndexLists.size > 1 ) {
      if ( seHs.noSolutionHasBeenFound ) {

        println( "printSomething2" )

        val allowedClausesWithIndexLists: Set[ClauseWithIndexLists] = checkAndBuildAllowedClausesHead(
          literalsWithIndexLists,
          seHs
        )

        println( "Clauses" )
        for ( clause <- allowedClausesWithIndexLists ) {
          println( clause.formula )
        }

        if ( seHs.noSolutionHasBeenFound ) {

          println( "printSomething3" )

          for ( numberOfClauses <- 2 to allowedClausesWithIndexLists.size; if seHs.noSolutionHasBeenFound ) {
            for ( subset <- allowedClausesWithIndexLists.subsets( numberOfClauses ); if seHs.noSolutionHasBeenFound ) {
              val clausesWithIndexLists = new ClausesWithIndexLists( subset.toList )
              if ( clausesWithIndexLists.isSolution ) {
                seHs.noSolutionHasBeenFound = false
                seHs.balancedSolution = Option( clausesWithIndexLists.formula )
              }
              println( "Checked Formula" )
              println( clausesWithIndexLists.formula )
            }
          }
        }
      }
    }

    println( "printSomething1" )

    /*
    val allowedClausesIndex: ( List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = allowedClausesWithIndex(
      unifiedLiterals,
      DNTAList,
      seHs,
      nameOfUniversalVariableChecked,
      nameOfExistentialVariableChecked
    )

    if ( seHs.noSolutionHasBeenFound ) {
      for ( subsetSize <- 2 to allowedClausesIndex.length; if ( seHs.noSolutionHasBeenFound ) ) {
        for ( subset <- allowedClausesIndex.toSet.subsets( subsetSize ); if ( seHs.noSolutionHasBeenFound ) ) {
          if ( checkCombinedClauses( DNTAList.length, subset.toList ) ) {
            seHs.noSolutionHasBeenFound = false
            val ( clauses, _, _ ) = subset.toList.unzip3
            val clausesAsFormula = clauses.map( clause => clause.toList ).map( clause => And( clause ) )

            seHs.balancedSolution = Option( Or( clausesAsFormula ) )

          }
        }
      }
    }
    */

    if ( !seHs.noSolutionHasBeenFound ) {
      seHs.balancedSolution
    } else {
      None
    }

  }

  private def checkAndBuildAllowedClausesHead(
    literalsWithIndexLists: Set[LiteralWithIndexLists],
    seHs:                   pi2SeHs
  ): ( Set[ClauseWithIndexLists] ) = {

    var allowedClausesWithIndexListsMutable = scala.collection.mutable.Set[ClauseWithIndexLists]()
    val literalsWithIndexListsMutable = scala.collection.mutable.Set( literalsWithIndexLists.toList: _* )

    for ( literalWithIndexLists <- literalsWithIndexLists ) {
      val clause = new ClauseWithIndexLists( List( literalWithIndexLists ) )
      if ( clause.isAllowed ) {
        allowedClausesWithIndexListsMutable += clause
      } else if ( !clause.isAllowedAtLeastAsSubformula ) {
        literalsWithIndexListsMutable -= literalWithIndexLists
      }
    }

    checkAndBuildAllowedClauses(
      literalsWithIndexListsMutable,
      allowedClausesWithIndexListsMutable,
      seHs,
      2
    ).toSet

  }

  private def checkAndBuildAllowedClauses(
    literalsWithIndexLists:       scala.collection.mutable.Set[LiteralWithIndexLists],
    allowedClausesWithIndexLists: scala.collection.mutable.Set[ClauseWithIndexLists],
    seHs:                         pi2SeHs,
    subsetSize:                   Int
  ): ( scala.collection.mutable.Set[ClauseWithIndexLists] ) = {

    for ( subset <- literalsWithIndexLists.subsets( subsetSize ); if seHs.noSolutionHasBeenFound ) {
      val clauseWithIndexLists = new ClauseWithIndexLists( subset.toList )
      if ( clauseWithIndexLists.isAllowed ) {
        allowedClausesWithIndexLists += clauseWithIndexLists
        val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
        if ( clausesWithIndexLists.isSolution ) {
          seHs.noSolutionHasBeenFound = false
          seHs.balancedSolution = Option( clausesWithIndexLists.formula )
        }
      } else if ( !clauseWithIndexLists.isAllowedAtLeastAsSubformula ) {
        for ( literal <- subset ) {
          literalsWithIndexLists -= literal
        }
      }
      println( "clause" )
      println( clauseWithIndexLists.formula )
      println( "noSolutionHasBeenFound" )
      println( seHs.noSolutionHasBeenFound )
      println( "isAllowedAsSubformula" )
      println( clauseWithIndexLists.isAllowedAtLeastAsSubformula )
      println( "isAllowed" )
      println( clauseWithIndexLists.isAllowed )
    }

    println( allowedClausesWithIndexLists )
    //println( subsetSize )

    if ( seHs.noSolutionHasBeenFound && ( 2 > subsetSize ) ) { // if ( seHs.noSolutionHasBeenFound && ( literalsWithIndexLists.size > subsetSize ) ) {
      checkAndBuildAllowedClauses(
        literalsWithIndexLists,
        allowedClausesWithIndexLists,
        seHs,
        subsetSize + 1
      )
    } else {
      allowedClausesWithIndexLists
    }

  }

  private def computeTheIndexListsForTheLiterals(
    unifiedLiterals:       Set[FOLFormula],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    y:                     FOLVar,
    x:                     FOLVar
  ): ( Set[LiteralWithIndexLists] ) = {

    val literalWithIndexListsSet = scala.collection.mutable.Set[LiteralWithIndexLists]()

    for ( literal <- unifiedLiterals; if seHs.noSolutionHasBeenFound ) {

      var leafOfIndexList: List[LeafIndex] = Nil

      for ( leaf <- nonTautologicalLeaves ) {

        val leafIndex = new LeafIndex( Set(), Set() )

        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs = Substitution( ( x, seHs.universalEigenvariable ), ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = subs( literal ).asInstanceOf[FOLFormula] +: Sequent()
          if ( subsetSequent.isSubsetOf( leaf ) ) {
            leafIndex.oneToPList += existsIndex
          }
        }

        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution( ( x, seHs.substitutionsForAlpha( forallIndex ) ), ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = Neg( subs( literal ).asInstanceOf[FOLFormula] ) +: Sequent()
          if ( !leaf.intersect( subsetSequent ).isEmpty ) {
            leafIndex.oneToMList += forallIndex
          }

        }

        leafOfIndexList = leafOfIndexList :+ leafIndex

      }

      val literalWithIndexLists = new LiteralWithIndexLists( literal, leafOfIndexList, nonTautologicalLeaves.length )
      literalWithIndexListsSet += literalWithIndexLists

      val clausesWithIndexLists = new ClausesWithIndexLists( List( new ClauseWithIndexLists( List( literalWithIndexLists ) ) ) )
      if ( clausesWithIndexLists.isSolution ) {
        seHs.noSolutionHasBeenFound = false
        seHs.balancedSolution = Option( clausesWithIndexLists.formula )
      }

    }

    literalWithIndexListsSet.toSet

  }

  private def allowedClausesWithIndex(
    literals:              Set[FOLFormula],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    x:                     FOLVar,
    y:                     FOLVar
  ): ( List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = {

    var clausesPlusIndex = scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )]()
    val literalsBuffer = scala.collection.mutable.Set( literals.toList: _* )

    clausesPlusIndex = recursionAllowedClausesWithIndexOld( 1, literalsBuffer, clausesPlusIndex, nonTautologicalLeaves, seHs, x, y )

    clausesPlusIndex.toList
  }

  private def recursionAllowedClausesWithIndexOld(
    subsetSize:            Int,
    literals:              scala.collection.mutable.Set[FOLFormula],
    clausesPlusIndex:      scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )],
    nonTautologicalLeaves: List[Sequent[FOLFormula]],
    seHs:                  pi2SeHs,
    x:                     FOLVar,
    y:                     FOLVar
  ): ( scala.collection.mutable.Set[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )] ) = {

    for ( subset <- literals.subsets( subsetSize ); if seHs.noSolutionHasBeenFound ) {

      var exists = List[Int]()
      var indexList = List[( Int, List[Int] )]()

      for ( leaf <- nonTautologicalLeaves ) {

        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs = Substitution( ( x, seHs.universalEigenvariable ), ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          var subsetSequent: Sequent[FOLFormula] = Sequent()
          for ( ele <- subset ) {
            subsetSequent = subs( ele ).asInstanceOf[FOLFormula] +: subsetSequent
          }

          if ( subsetSequent.isSubsetOf( leaf ) ) {
            exists = exists :+ nonTautologicalLeaves.indexOf( leaf ) // leaf + List[IndexAlphaTiAlpha] + List[IndexRiBetai]
          }
        }

        var betaIndexSet = List[Int]()
        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution( ( x, seHs.substitutionsForAlpha( forallIndex ) ), ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          var subsetSequent: Sequent[FOLFormula] = Sequent()
          for ( ele <- subset ) {
            subsetSequent = Neg( subs( ele ).asInstanceOf[FOLFormula] ) +: subsetSequent
          }

          if ( !leaf.intersect( subsetSequent ).isEmpty ) {
            betaIndexSet = betaIndexSet :+ forallIndex
          }

        }

        val newElement: ( Int, List[Int] ) = ( nonTautologicalLeaves.indexOf( leaf ), betaIndexSet )
        indexList = indexList :+ newElement

      }

      // Collects all necessary information and deletes unnecessary literals
      //////////////////////////////////////////////////////////////////////
      if ( exists.nonEmpty ) {
        val clausePlusIndex = ( subset.toSet, exists, indexList )
        clausesPlusIndex += clausePlusIndex
      } else {
        subset.foreach( literal => literals -= literal )
      }

      // Checks whether a single clause is already a solution
      ///////////////////////////////////////////////////////
      if ( exists.nonEmpty ) {

        var existsIndex: Boolean = true
        val ( _, i ) = indexList.unzip // ( i, _ )

        for ( leafIndex <- 0 until nonTautologicalLeaves.length; if existsIndex ) {
          if ( i( leafIndex ).isEmpty || !exists.contains( leafIndex ) ) { // !i.contains( leafIndex )
            existsIndex = false
          }
        }

        if ( existsIndex ) {

          seHs.noSolutionHasBeenFound = false
          seHs.balancedSolution = Option( And( subset ) )

        }

      }

    }

    if ( literals.toList.length <= subsetSize ) {
      clausesPlusIndex
    } else if ( !seHs.noSolutionHasBeenFound ) {
      clausesPlusIndex
    } else {
      recursionAllowedClausesWithIndexOld( subsetSize + 1, literals, clausesPlusIndex, nonTautologicalLeaves, seHs, x, y )
    }
  }

  private def checkCombinedClauses(
    numberOfDNTAs:             Int,
    setOfClausesPlusIndexSets: List[( Set[FOLFormula], List[Int], List[( Int, List[Int] )] )]
  ): ( Boolean ) = {

    var isSolution: Boolean = true

    val ( _, existsIndexList, betaIndexList ) = setOfClausesPlusIndexSets.unzip3

    for ( i <- 0 until numberOfDNTAs; if isSolution ) {
      if ( !existsIndexList.flatten.contains( i ) ) {
        isSolution = false
      }
    }

    if ( isSolution ) {
      var list: List[Int] = Nil
      for ( i <- 0 until numberOfDNTAs ) {
        list = list :+ i
      }
      val intersections = new Array[List[Int]]( numberOfDNTAs )
      var foundEmptyIntersection: Boolean = false
      isSolution = betaIndexList.forall( element => {
        element.forall( ele => {
          val ( leafIndex, satisfiedOnes ) = ele
          if ( foundEmptyIntersection ) {
            false
          } else if ( list.contains( leafIndex ) ) {
            list = list.filterNot( t => t == leafIndex )
            intersections( leafIndex ) = satisfiedOnes
            if ( intersections( leafIndex ).isEmpty ) {
              foundEmptyIntersection = true
              false
            } else {
              true
            }
          } else {
            intersections( leafIndex ) = intersections( leafIndex ).intersect( satisfiedOnes )
            if ( intersections( leafIndex ).isEmpty ) {
              foundEmptyIntersection = true
              false
            } else {
              true
            }
          }
        } )
      } )
    }

    isSolution

  }

}