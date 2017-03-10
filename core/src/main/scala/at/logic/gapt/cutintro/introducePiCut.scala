package at.logic.gapt.cutintro
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ FOLClause, Sequent }

/**
 * Created by root on 26.01.17.
 */
case class Pi2SeHs(
    val reducedRepresentation:         Sequent[FOLFormula], // F[x\U_1] |- G[y\U_2]
    val universalEigenvariable:        FOLVar, // alpha
    val existentialEigenvariables:     List[FOLVar], // beta_1,...,beta_m
    val substitutionsForAlpha:         List[Expr], // r_1,...,r_m
    val substitutionsForBetaWithAlpha: List[Expr] // t_1(alpha),...,t_p(alpha)
) {

  require( existentialEigenvariables.length == substitutionsForAlpha.length )

  val multiplicityOfAlpha: Int = substitutionsForAlpha.length // m
  val multiplicityOfBeta: Int = substitutionsForBetaWithAlpha.length // p
  var balancedSolution: Option[FOLFormula] = None
  var noSolutionHasBeenFound: Boolean = true

  // (alpha,r_1),...,(alpha,r_m)
  //////////////////////////////
  val substitutionPairsAlpha: List[( Expr, Expr )] = {

    substitutionsForAlpha.map( instance => ( universalEigenvariable, instance ) )
    /*
    val substitutionPairsAlpha = scala.collection.mutable.Set[( Expr, Expr )]()
    substitutionsForAlpha.foreach( instance => {
      val buffer: ( Expr, Expr ) = ( universalEigenvariable, instance )
      substitutionPairsAlpha += buffer
    } )
    substitutionPairsAlpha.toList
    */
  }

  // (beta_i,t_1(alpha)),...,(beta_i,t_p(alpha))
  //////////////////////////////////////////////
  def substitutionPairsBetaI( index: Int ): List[( Expr, Expr )] = {

    substitutionsForBetaWithAlpha.map( instanceB => ( existentialEigenvariables( index - 1), instanceB ) )
    /*
    val substitutionPairsBetaI = scala.collection.mutable.Set[( Expr, Expr )]()
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      val buffer: ( Expr, Expr ) = ( existentialEigenvariables( index - 1 ), instanceB )
      substitutionPairsBetaI += buffer
    } )
    substitutionPairsBetaI.toList
    */
  }

  // (beta_1,t_1(alpha)),...,(beta_1,t_p(alpha)),
  //                     ...                    ,
  // (beta_m,t_1(alpha)),...,(beta_m,t_p(alpha))
  ///////////////////////////////////////////////
  val substitutionPairsBeta: List[( Expr, Expr )] = {

    (
      for ( index <- 1 to multiplicityOfAlpha )
        yield substitutionPairsBetaI( multiplicityOfAlpha - index + 1 )
    ).toList.flatten
    /*
    val substitutionPairsBeta = scala.collection.mutable.Set[( Expr, Expr )]()
    for ( index <- 1 to multiplicityOfAlpha ) {
      substitutionPairsBeta ++= substitutionPairsBetaI( multiplicityOfAlpha - index + 1 )
    }
    substitutionPairsBeta.toSet
    */
  }

  val productionRulesXS: List[( Expr, Expr )] = substitutionPairsAlpha ++ substitutionPairsAlpha.map( _.swap )

  val productionRulesYS: List[( Expr, Expr )] = substitutionPairsBeta ++ substitutionPairsBeta.map( _.swap )

  // (alpha->r_1),...,(alpha->r_m)
  ////////////////////////////////
  val substitutionsAlpha: List[Substitution] = {

    substitutionsForAlpha.map( instanceA => Substitution( universalEigenvariable, instanceA ) )

    /*
    val substitutionsAlpha = scala.collection.mutable.ListBuffer[Substitution]()
    substitutionsForAlpha.foreach( instanceA => {
      substitutionsAlpha += Substitution( universalEigenvariable, instanceA )
    } )
    substitutionsAlpha.toList
    */
  }

  // (beta_i->t_1(r_i)),...,(beta_i->t_p(r_i))
  ////////////////////////////////////////////
  def substitutionsBetaI( index: Int ): List[Substitution] = {

    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) )
    substitutionsForBetaWithAlpha.map( instanceB => Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) ) )

    /*
    val substitutionsBeta = scala.collection.mutable.ListBuffer[Substitution]()
    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) ) // (alpha->r_i)
    substitutionsForBetaWithAlpha.foreach( instanceB => {
      substitutionsBeta += Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) )
    } )
    substitutionsBeta.toList
    */
  }

  private def substituteRightSideOnce( sequent: Sequent[Formula], index: Int ): Sequent[Formula] = {

    var resultingSequent: Sequent[Formula] = Sequent()

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

  private def substituteLeftSideOnce( sequent: Sequent[Formula], index: Int ): Sequent[Formula] = {

    var resultingSequent: Sequent[Formula] = Sequent()

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
  def herbrandSequent(): Sequent[Formula] = {

    var herbrandSequent: Sequent[Formula] = Sequent() :++ reducedRepresentation.succedent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteRightSideOnce( herbrandSequent, multiplicityOfAlpha - indexM )
    }

    reducedRepresentation.antecedent.foreach( formula => {
      substitutionsForAlpha.foreach( instanceA => {
        val subs: Substitution = Substitution( universalEigenvariable, instanceA )
        herbrandSequent = subs( formula ) +: herbrandSequent
      } )
    } )

    val sequent: Sequent[Formula] = herbrandSequent

    for ( indexM <- 0 until multiplicityOfAlpha ) {
      herbrandSequent = substituteLeftSideOnce( herbrandSequent.antecedent ++: Sequent(), multiplicityOfAlpha - indexM ) :++ sequent.succedent
    }

    herbrandSequent
  }

  // The reduced representation as a formula
  //////////////////////////////////////////
  val reducedRepresentationToFormula: FOLFormula = reducedRepresentation.toImplication

  val literalsInTheDNTAsAndTheDNTAs: ( Set[FOLFormula], List[Sequent[FOLFormula]] ) = {

    val literals = scala.collection.mutable.Set[FOLFormula]()
    val DNTA = scala.collection.mutable.Set[Sequent[FOLFormula]]()

    CNFp( this.reducedRepresentationToFormula ).foreach( clause => if ( !clause.isTaut ) {
      val NTAClause: Sequent[FOLFormula] = clause.succedent.map( literal => Neg( literal ) ) ++: clause.antecedent ++: Sequent()
      val DNTABuffer = DNTA.toList
      var dontAdd: Boolean = false
      DNTABuffer.foreach( DNTAClause => {
        if ( !dontAdd ) {
          if ( NTAClause.isSubsetOf( DNTAClause ) ) {
            DNTA -= DNTAClause
          } else if ( DNTAClause.isSubsetOf( NTAClause ) ) {
            dontAdd = true
          }
        }
      } )
      if ( !dontAdd ) {
        DNTA += NTAClause // define for fol and hol sequents
      }
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )

    val DNTAList = DNTA.toList

    ( literals.toSet, DNTAList )
  }

  def language: ( Set[Expr] ) = {

    val ( literals, _ ) = this.literalsInTheDNTAsAndTheDNTAs
    literals.map( literal => {
      literal match {
        case Neg( t ) => {
          val Apps( name, _ ) = t
          name
        }
        case t => {
          val Apps( name, _ ) = t
          name
        }
      }
    } )
  }

  def theDNTAsInTheLanguage( unifiedLiterals: Set[FOLFormula] ): ( List[Sequent[FOLFormula]] ) = {

    val ( _, oldDNTAs ) = this.literalsInTheDNTAsAndTheDNTAs
    val newDNTAs = oldDNTAs.map( leaf => {
      leaf.antecedent.filter( literal => {
        literal match {
          case Neg( t ) => {
            val isInLanguage: Boolean = unifiedLiterals.exists( opponent => {
              val Apps( nameOfLiteral, _ ) = t
              val Apps( nameOfOpponent, _ ) = opponent
              nameOfLiteral.syntaxEquals( nameOfOpponent )
            } )
            isInLanguage
          }
          case t => {
            val isInLanguage: Boolean = unifiedLiterals.exists( opponent => {
              val Apps( nameOfLiteral, _ ) = t
              val Apps( nameOfOpponent, _ ) = opponent
              nameOfLiteral.syntaxEquals( nameOfOpponent )
            } )
            isInLanguage
          }
        }
      } ) ++: Sequent()
    } )

    val DNTA = scala.collection.mutable.Set( newDNTAs.head )
    newDNTAs.tail.foreach( DNTAClause => {
      var dontAdd: Boolean = false
      val DNTABuffer = DNTA
      DNTABuffer.foreach( existingClause => {
        if ( !dontAdd ) {
          if ( existingClause.isSubsetOf( DNTAClause ) ) {
            DNTA -= existingClause
          } else if ( DNTAClause.isSubsetOf( existingClause ) ) {
            dontAdd = true
          }
        }
      } )
      if ( !dontAdd ) {
        DNTA += DNTAClause
      }
    } )

    DNTA.toList

  }

  val sortAndAtomize: ( Set[FOLFormula], Set[FOLFormula] ) = {

    val ( literals, _ ) = this.literalsInTheDNTAsAndTheDNTAs
    val posLiterals: scala.collection.mutable.Set[FOLFormula] = scala.collection.mutable.Set()
    val negLiterals: scala.collection.mutable.Set[FOLFormula] = scala.collection.mutable.Set()

    for ( literal <- literals ) {

      literal match {
        case Neg( t ) => negLiterals += t
        case _        => posLiterals += literal
      }

    }

    ( posLiterals.toSet, negLiterals.toSet )

  }

}

class LeafIndex(
  val oneToMList: Set[Int],
  val oneToPList: Set[Int]
) {}

class LiteralWithIndexLists(
    val literal:            FOLFormula,
    val leafIndexList:      List[LeafIndex],
    val numberOfDNTAs:      Int,
    val foundNonEmptyPList: Boolean,
    val foundEmptyMList:    Boolean
) {
  // require( numberOfDNTAs == leafIndexList.length )
}

class ClauseWithIndexLists(
    val literals: List[LiteralWithIndexLists]
) {

  // require( literals.tail.forall( _.numberOfDNTAs == literals.head.numberOfDNTAs ) )

  def numberOfDNTAs: Int = this.literals.head.numberOfDNTAs

  val leafIndexListClause: List[LeafIndex] = {

    if ( literals.length == 1 ) {
      literals.head.leafIndexList
    } else {
      var leafIndexListClauseBuffer: List[LeafIndex] = Nil
      for ( leafNumber <- 0 until this.literals.head.numberOfDNTAs ) {
        var leafIndexListClauseBufferM = this.literals.head.leafIndexList( leafNumber ).oneToMList
        var leafIndexListClauseBufferP = this.literals.head.leafIndexList( leafNumber ).oneToPList
        this.literals.tail.foreach( literal => {
          leafIndexListClauseBufferM = leafIndexListClauseBufferM.union( literal.leafIndexList( leafNumber ).oneToMList )
          leafIndexListClauseBufferP = leafIndexListClauseBufferP.intersect( literal.leafIndexList( leafNumber ).oneToPList )
        } )
        val leafIn = new LeafIndex( leafIndexListClauseBufferM, leafIndexListClauseBufferP )
        leafIndexListClauseBuffer = leafIndexListClauseBuffer :+ leafIn
      }
      leafIndexListClauseBuffer
    }
  }

  val isAllowed: Boolean = {

    if ( literals.length == 1 ) {
      literals.head.foundNonEmptyPList
    } else {
      var bool: Boolean = false
      this.leafIndexListClause.foreach( leafNumber => {
        if ( leafNumber.oneToPList.nonEmpty ) {
          bool = true
        }
      } )
      bool
    }
  }

  val isAllowedAtLeastAsSubformula: Boolean = {

    var bool: Boolean = true
    if ( this.isAllowed ) {
      if ( literals.length == 1 ) {
        bool = !literals.head.foundEmptyMList
      } else {
        this.leafIndexListClause.foreach( leafNumber => {
          if ( leafNumber.oneToMList.isEmpty ) {
            bool = false
          }
        } )
      }
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

  private def leafIndexListClauses: List[LeafIndex] = {

    if ( clauses.length == 1 ) {
      clauses.head.leafIndexListClause
    } else {
      var emptyList: Boolean = false
      var leafIndexListClausesBuffer: List[LeafIndex] = Nil
      for ( leafNumber <- 0 until this.clauses.head.numberOfDNTAs; if !emptyList ) {
        var leafIndexListClausesBufferM = this.clauses.head.leafIndexListClause( leafNumber ).oneToMList
        var leafIndexListClausesBufferP = this.clauses.head.leafIndexListClause( leafNumber ).oneToPList
        this.clauses.tail.foreach( clause => {
          if ( !emptyList ) {
            leafIndexListClausesBufferM = leafIndexListClausesBufferM.intersect( clause.leafIndexListClause( leafNumber ).oneToMList )
            leafIndexListClausesBufferP = leafIndexListClausesBufferP.union( clause.leafIndexListClause( leafNumber ).oneToPList )
          }
          if ( leafIndexListClausesBufferM.isEmpty ) {
            emptyList = true
          }
        } )
        val leafIn = new LeafIndex( leafIndexListClausesBufferM, leafIndexListClausesBufferP )
        leafIndexListClausesBuffer = leafIndexListClausesBuffer :+ leafIn
      }
      leafIndexListClausesBuffer
    }
  }

  def isSolution: Boolean = {

    var bool: Boolean = true
    if ( clauses.length == 1 ) {
      if ( clauses.head.isAllowedAtLeastAsSubformula ) {
        this.leafIndexListClauses.forall( leafNumber => {
          if ( leafNumber.oneToPList.isEmpty ) {
            bool = false
          } else if ( leafNumber.oneToMList.isEmpty ) {
            bool = false
          }
          bool
        } )
      } else {
        false
      }
    } else {
      this.leafIndexListClauses.forall( leafNumber => {
        if ( leafNumber.oneToPList.isEmpty ) {
          bool = false
        } else if ( leafNumber.oneToMList.isEmpty ) {
          bool = false
        }
        bool
      } )
    }
  }

  def formula: FOLFormula = {

    var formulaBuffer: FOLFormula = this.clauses.head.formula
    this.clauses.tail.foreach( clause => formulaBuffer = Or( formulaBuffer, clause.formula ) )
    formulaBuffer
  }

}

object introducePi2Cut {

  def apply(
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: FOLVar  = fov"yCut",
    nameOfUniversalVariable:   FOLVar  = fov"xCut"
  ): ( Option[FOLFormula], FOLVar, FOLVar ) = {

    val nameOfExistentialVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfExistentialVariable )
    val nameOfUniversalVariableChecked = rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfUniversalVariable )

    val unifiedLiterals: Set[FOLFormula] = gStarUnify(
      seHs,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    /*
    // There is no need in the given examples (see IntroducePiCutTest.scala). In case of examples with a large theory,
    // the following code decreases the number of DNTAs we have to look at.
    val ( literals, _ ) = seHs.literalsInTheDNTAsAndTheDNTAs
    val languageSize = literals.map(literal=>{
      literal match {
        case Neg( t ) => {
          val Apps(name,_) = t
          name
        }
        case t => {
          val Apps(name,_) = t
          name
        }
      }
    }).size
    if (languageSize<seHs.language.size) {
      val dNTAList = seHs.theDNTAsInTheLanguage( unifiedLiterals )
    } else {
      val ( _, dNTAList ) = seHs.literalsInTheDNTAsAndTheDNTAs
    }
    */

    val ( _, dNTAList ) = seHs.literalsInTheDNTAsAndTheDNTAs

    val literalsWithIndexLists: Set[LiteralWithIndexLists] = computeTheIndexListsForTheLiterals(
      unifiedLiterals,
      dNTAList,
      seHs,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked
    )

    var numberOfAllowedClauses: Option[Int] = None
    var numberOfCheckedFormulas: Int = literalsWithIndexLists.size

    if ( literalsWithIndexLists.size > 1 ) {
      if ( seHs.noSolutionHasBeenFound ) {

        val allowedClausesWithIndexLists: Set[ClauseWithIndexLists] = checkAndBuildAllowedClausesHead(
          literalsWithIndexLists,
          seHs
        )

        numberOfAllowedClauses = Option( allowedClausesWithIndexLists.size )
        numberOfCheckedFormulas = allowedClausesWithIndexLists.size

        if ( seHs.noSolutionHasBeenFound ) {
          for ( numberOfClauses <- 2 to allowedClausesWithIndexLists.size; if seHs.noSolutionHasBeenFound ) {
            for ( subset <- allowedClausesWithIndexLists.subsets( 2 ); if seHs.noSolutionHasBeenFound ) { // !!!!!!!!!!!!!!!!!!!!! for testing set to two
              val clausesWithIndexLists = new ClausesWithIndexLists( subset.toList )
              if ( clausesWithIndexLists.isSolution ) {
                seHs.noSolutionHasBeenFound = false
                seHs.balancedSolution = Option( clausesWithIndexLists.formula )
              }
              numberOfCheckedFormulas += 1
            }
          }
        }
      }
    }

    // println( "Number of non-tautological leaves" )
    // println( dNTAList.length )
    // println( "Number of unified literals" )
    // println( unifiedLiterals.size )
    // numberOfAllowedClauses match {
    //   case Some( t ) => {
    //     println( "Number of allowed clauses" )
    //     println( t )
    //   }
    //   case None => println( "No 'allowed clauses' were computed" )
    // }
    // println( "Number of checked Formulas" )
    // println( numberOfCheckedFormulas )

    if ( !seHs.noSolutionHasBeenFound ) {
      ( seHs.balancedSolution, nameOfExistentialVariableChecked, nameOfUniversalVariableChecked )
    } else {
      ( None, nameOfExistentialVariableChecked, nameOfUniversalVariableChecked )
    }

  }

  private def checkAndBuildAllowedClausesHead(
    literalsWithIndexLists: Set[LiteralWithIndexLists],
    seHs:                   Pi2SeHs
  ): ( Set[ClauseWithIndexLists] ) = {

    var allowedClausesWithIndexListsMutable = scala.collection.mutable.Set[ClauseWithIndexLists]()
    val literalsWithIndexListsMutable = scala.collection.mutable.Set( literalsWithIndexLists.toList: _* )

    for ( literalWithIndexLists <- literalsWithIndexLists ) {
      val clause = new ClauseWithIndexLists( List( literalWithIndexLists ) )
      val ( clauseIsUnnecessary, listOfUnnecessaryClauses ) = checkNecessityOfNewAndOldClause( clause, allowedClausesWithIndexListsMutable.toList )
      if ( !clauseIsUnnecessary ) {
        allowedClausesWithIndexListsMutable += clause
        if ( !clause.isAllowedAtLeastAsSubformula && !clause.isAllowed ) {
          literalsWithIndexListsMutable -= literalWithIndexLists
        }
        for ( unnecessaryClause <- listOfUnnecessaryClauses ) {
          allowedClausesWithIndexListsMutable -= unnecessaryClause
        }
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
    seHs:                         Pi2SeHs,
    subsetSize:                   Int
  ): ( scala.collection.mutable.Set[ClauseWithIndexLists] ) = {

    for ( subset <- literalsWithIndexLists.subsets( subsetSize ); if seHs.noSolutionHasBeenFound ) {
      val clauseWithIndexLists = new ClauseWithIndexLists( subset.toList )
      if ( clauseWithIndexLists.isAllowed ) {
        val ( clauseIsUnnecessary, listOfUnnecessaryClauses ) = checkNecessityOfNewAndOldClause( clauseWithIndexLists, allowedClausesWithIndexLists.toList )
        if ( !clauseIsUnnecessary ) {
          allowedClausesWithIndexLists += clauseWithIndexLists
          val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
          if ( clausesWithIndexLists.isSolution ) {
            seHs.noSolutionHasBeenFound = false
            seHs.balancedSolution = Option( clausesWithIndexLists.formula )
          }
          for ( unnecessaryClause <- listOfUnnecessaryClauses ) {
            allowedClausesWithIndexLists -= unnecessaryClause
          }
        }
      } else if ( !clauseWithIndexLists.isAllowedAtLeastAsSubformula ) {
        for ( literal <- subset ) {
          literalsWithIndexLists -= literal
        }
      }
    }

    if ( seHs.noSolutionHasBeenFound && ( literalsWithIndexLists.size > subsetSize ) ) {
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
    seHs:                  Pi2SeHs,
    y:                     FOLVar,
    x:                     FOLVar
  ): ( Set[LiteralWithIndexLists] ) = {

    val literalWithIndexListsSet = scala.collection.mutable.Set[LiteralWithIndexLists]()

    for ( literal <- unifiedLiterals; if seHs.noSolutionHasBeenFound ) {

      var foundEmptyMOrPList: Boolean = false
      var foundNonEmptyPList: Boolean = false
      var foundEmptyMList: Boolean = false
      var leafOfIndexList: List[LeafIndex] = Nil

      for ( leaf <- nonTautologicalLeaves ) {

        var leafIndexP = Set[Int]()
        var leafIndexM = Set[Int]()

        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs = Substitution( ( x, seHs.universalEigenvariable ), ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = subs( literal ).asInstanceOf[FOLFormula] +: Sequent()
          if ( subsetSequent.isSubsetOf( leaf ) ) {
            leafIndexP += existsIndex
          }
        }

        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution( ( x, seHs.substitutionsForAlpha( forallIndex ) ), ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          val subsetSequent: Sequent[FOLFormula] = Neg( subs( literal ).asInstanceOf[FOLFormula] ) +: Sequent()
          if ( !leaf.intersect( subsetSequent ).isEmpty ) {
            leafIndexM += forallIndex
          }

        }

        if ( leafIndexM.isEmpty ) {
          foundEmptyMList = true
          foundEmptyMOrPList = true
        } else if ( leafIndexP.isEmpty ) {
          foundEmptyMOrPList = true
        }
        if ( leafIndexP.nonEmpty ) {
          foundNonEmptyPList = true
        }
        val leafIndex = new LeafIndex( leafIndexM, leafIndexP )
        leafOfIndexList = leafOfIndexList :+ leafIndex

      }

      val literalWithIndexLists = new LiteralWithIndexLists(
        literal,
        leafOfIndexList,
        nonTautologicalLeaves.length,
        foundNonEmptyPList,
        foundEmptyMList
      )

      if ( foundNonEmptyPList ) {

        literalWithIndexListsSet += literalWithIndexLists

        if ( !foundEmptyMOrPList ) {
          val clauseWithIndexLists = new ClauseWithIndexLists( List( literalWithIndexLists ) )
          val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
          if ( clausesWithIndexLists.isSolution ) {
            seHs.noSolutionHasBeenFound = false
            seHs.balancedSolution = Option( clausesWithIndexLists.formula )
          }
        }
      }

    }

    literalWithIndexListsSet.toSet

  }

  private def checkNecessityOfNewAndOldClause(
    newClause:  ClauseWithIndexLists,
    oldClauses: List[ClauseWithIndexLists]
  ): ( Boolean, List[ClauseWithIndexLists] ) = {

    if ( oldClauses == Nil ) {
      ( false, Nil )
    } else {
      val clauseIsNotSubsetOfI = new Array[Boolean]( oldClauses.length )
      val iIsNotSubsetOfClause = new Array[Boolean]( oldClauses.length )

      for ( leafNumber <- 0 until newClause.numberOfDNTAs ) {
        for (
          oldClause <- oldClauses; if !clauseIsNotSubsetOfI( oldClauses.indexOf( oldClause ) ) ||
            !iIsNotSubsetOfClause( oldClauses.indexOf( oldClause ) )
        ) {

          if ( !clauseIsNotSubsetOfI( oldClauses.indexOf( oldClause ) ) ) {
            if ( !newClause.leafIndexListClause( leafNumber ).oneToMList.subsetOf( oldClause.leafIndexListClause( leafNumber ).oneToMList ) ||
              !newClause.leafIndexListClause( leafNumber ).oneToPList.subsetOf( oldClause.leafIndexListClause( leafNumber ).oneToPList ) ) {
              clauseIsNotSubsetOfI( oldClauses.indexOf( oldClause ) ) = true
            }
          }

          if ( !iIsNotSubsetOfClause( oldClauses.indexOf( oldClause ) ) ) {
            if ( !oldClause.leafIndexListClause( leafNumber ).oneToMList.subsetOf( newClause.leafIndexListClause( leafNumber ).oneToMList ) ||
              !oldClause.leafIndexListClause( leafNumber ).oneToPList.subsetOf( newClause.leafIndexListClause( leafNumber ).oneToPList ) ) {
              iIsNotSubsetOfClause( oldClauses.indexOf( oldClause ) ) = true
            }
          }
        }
      }

      var clauseIsUnnecessary: Boolean = false
      var listOfUnnecessaryClauses: List[ClauseWithIndexLists] = Nil
      for ( i <- 0 until oldClauses.length; if !clauseIsUnnecessary ) {
        if ( !clauseIsNotSubsetOfI( i ) ) {
          clauseIsUnnecessary = true
        } else if ( !iIsNotSubsetOfClause( i ) ) {
          listOfUnnecessaryClauses = listOfUnnecessaryClauses :+ oldClauses( i )
        }
      }

      ( clauseIsUnnecessary, listOfUnnecessaryClauses )
    }

  }

}