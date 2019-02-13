package gapt.cutintro
import gapt.expr._
import gapt.expr.hol.CNFp
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.proofs.{ FOLClause, Sequent }

/**
 * Schematic extended Herbrand sequent for schematic Pi-2 grammars
 * @param reducedRepresentation The schematic extended Herbrand sequent without placeholder
 *                              for the cut ( F[x\U_1] |- G[y\U_2] )
 * @param universalEigenvariable The variable that is introduced for the universally
 *                               quantified variable of the cut formula (alpha)
 * @param existentialEigenvariables The variables that are introduced for the existentially
 *                                  quantified variable of the cut
 *                                  formula (beta_1,...,beta_m)
 * @param substitutionsForAlpha The terms (except from the eigenvariable) that are introduced
 *                              for the universally quantified variable of
 *                              the cut formula (r_1,...,r_m)
 * @param substitutionsForBetaWithAlpha The terms (except from the eigenvariables) that are
 *                                      introduced for the existentially quantified variable
 *                                      of the cut formula independent from the existential
 *                                      eigenvariables (t_1(alpha),...,t_p(alpha))
 */
case class Pi2SeHs(
    reducedRepresentation:         Sequent[Formula], // F[x\U_1] |- G[y\U_2]
    universalEigenvariable:        Var, // alpha
    existentialEigenvariables:     List[Var], // beta_1,...,beta_m
    substitutionsForAlpha:         List[Expr], // r_1,...,r_m
    substitutionsForBetaWithAlpha: List[Expr] // t_1(alpha),...,t_p(alpha)
) {

  require( existentialEigenvariables.length == substitutionsForAlpha.length )

  /**
   * Number of substitutions for the eigenvariable of the universally quantified variable (m)
   */
  val multiplicityOfAlpha: Int = substitutionsForAlpha.length
  /**
   * Number of substitutions for the eigenvariables of the existentially quantified variable independent
   * from the substitution of the universal
   * eigenvariable (p)
   */
  val multiplicityOfBeta: Int = substitutionsForBetaWithAlpha.length

  /**
   * Pairs of the universal eigenvariable with the substitutions for the universal eigenvariable
   * ((alpha,r_1),...,(alpha,r_m))
   */
  val substitutionPairsAlpha: List[( Expr, Expr )] = {

    substitutionsForAlpha.map( instance => ( universalEigenvariable, instance ) )
  }

  /**
   * Pairs of a existential eigenvariable with the substitutions for this existential eigenvariable
   * ((beta_i,t_1(alpha)),...,(beta_i,t_p(alpha)) with i=index)
   * @param index Indicates the considered existential eigenvariable (1 <= index <= m)
   * @return
   */
  def substitutionPairsBetaI( index: Int ): List[( Expr, Expr )] = {

    require( 1 <= index && index <= this.multiplicityOfAlpha )
    substitutionsForBetaWithAlpha.map( instanceB => ( existentialEigenvariables( index - 1 ), instanceB ) )
  }

  /**
   * Pairs of the existential eigenvariables with the substitutions for the existential eigenvariables
   * ((beta_1,t_1(alpha)),...,(beta_1,t_p(alpha)),...,(beta_m,t_1(alpha)),...,(beta_m,t_p(alpha)))
   */
  val substitutionPairsBeta: List[( Expr, Expr )] = {

    (
      for ( index <- 1 to multiplicityOfAlpha )
        yield substitutionPairsBetaI( multiplicityOfAlpha - index + 1 ) ).toList.flatten
  }

  /**
   * List of all substitution pairs (alpha,r_i) and (r_i,alpha)
   */
  val productionRulesXS: List[( Expr, Expr )] = substitutionPairsAlpha ++ substitutionPairsAlpha.map( _.swap )

  /**
   * List of all substitution pairs (beta_j,t_i(alpha)) and (t_i(alpha),beta_j)
   */
  val productionRulesYS: List[( Expr, Expr )] = substitutionPairsBeta ++ substitutionPairsBeta.map( _.swap )

  /**
   * List of substitutions ((alpha->r_1),...,(alpha->r_m))
   */
  val substitutionsAlpha: List[Substitution] = {

    substitutionsForAlpha.map( instanceA => Substitution( universalEigenvariable, instanceA ) )
  }

  /**
   * List of substitutions ((beta_i->t_1(r_i)),...,(beta_i->t_p(r_i)) with i=index)
   * @param index Indicates the considered existential eigenvariable (1 <= index <= m)
   * @return
   */
  def substitutionsBetaI( index: Int ): List[Substitution] = {

    require( 1 <= index && index <= this.multiplicityOfAlpha )
    val subs: Substitution = Substitution( universalEigenvariable, substitutionsForAlpha( index - 1 ) )
    substitutionsForBetaWithAlpha.map( instanceB =>
      Substitution( existentialEigenvariables( index - 1 ), subs( instanceB ) ) )
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

  /**
   * Computes the Herbrand sequent that corresponds to the schematic Pi-2 grammar (F[x\T_1] |- G[y\T_2])
   * @return
   */
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
      herbrandSequent = substituteLeftSideOnce(
        herbrandSequent.antecedent ++: Sequent(),
        multiplicityOfAlpha - indexM ) :++ sequent.succedent
    }

    herbrandSequent
  }

  /**
   * Transforms the reduced representation from a sequent to a formula
   */
  val reducedRepresentationToFormula: Formula = reducedRepresentation.toImplication

  /**
   * Computes simultaneously a set of all atoms occurring in the leaves of the reduced representation (the atoms are negated if they
   * occur on the right side of the sequent) and a list of all relevant normalized (everything is shifted to the left side) leaves
   * of the reduced representation
   */
  val literalsInTheDNTAsAndTheDNTAs: ( Set[Formula], List[Sequent[Formula]] ) = {

    val literals = scala.collection.mutable.Set[Formula]()
    val DNTA = scala.collection.mutable.Set[Sequent[Formula]]()

    CNFp( this.reducedRepresentationToFormula ).foreach( clause => if ( !clause.isTaut ) {
      val NTAClause: Sequent[Formula] =
        clause.succedent.map( literal => Neg( literal ) ) ++: clause.antecedent ++: Sequent()
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
        DNTA += NTAClause
      }
      clause.antecedent.foreach( atom => literals += atom )
      clause.succedent.foreach( atom => literals += Neg( atom ) )
    } )

    val DNTAList = DNTA.toList

    ( literals.toSet, DNTAList )
  }

  /**
   * The set of all relevant normalized (everything is shifted to the left side) leaves
   */
  val dualNonTautologicalAxioms: List[Sequent[Formula]] = {

    val ( _, dNTAs ) = this.literalsInTheDNTAsAndTheDNTAs
    dNTAs

  }

  /**
   * Three sets A,B,N containing all atoms occurring in the leaves of the reduced
   * representation (the atoms are negated if they occur on
   * the right side of the sequent) such that in all atoms (literals) of N no
   * eigenvariables occur, in all atoms (literals) of A only the
   * universal eigenvariable occur, and in all atoms (literals) of B only the
   * existential eigenvariables occur
   */
  val literalsInTheDNTAs: ( Set[Formula], Set[Formula], Set[Formula] ) = {

    val ( literals, _ ) = this.literalsInTheDNTAsAndTheDNTAs
    val alpha = scala.collection.mutable.Set[Formula]()
    val beta = scala.collection.mutable.Set[Formula]()
    val gamma = scala.collection.mutable.Set[Formula]()

    literals.foreach( literal => {
      if ( literal.contains( this.universalEigenvariable ) ) {
        if ( !this.existentialEigenvariables.exists( exEi => literal.contains( exEi ) ) ) {
          alpha += literal
        }
      } else if ( this.existentialEigenvariables.exists( exEi => literal.contains( exEi ) ) ) {
        beta += literal
      } else {
        gamma += literal
      }
    } )

    ( alpha.toSet, beta.toSet, gamma.toSet )
  }

  /**
   * List of all relevant normalized (everything is shifted to the left side) leaves of the reduced representation
   * in a reduced signature/language that contains the unified literals (work in progress)
   * @param unifiedLiterals A set of formulas (unified literals) that define the reduced signature/language
   * @return
   */
  def theDNTAsInTheLanguage( unifiedLiterals: Set[Formula] ): ( List[Sequent[Formula]] ) = {

    val newDNTAs = this.dualNonTautologicalAxioms.map( leaf => {
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

  /**
   * Computes two sets of atoms P,N for a given set of literals such that P contains
   * all positive literals and N all atoms of the negative literals
   * @param literals
   * @return
   */
  def sortAndAtomize( literals: Set[Formula] ): ( Set[Formula], Set[Formula] ) = {

    val posLiterals: scala.collection.mutable.Set[Formula] = scala.collection.mutable.Set()
    val negLiterals: scala.collection.mutable.Set[Formula] = scala.collection.mutable.Set()

    for ( literal <- literals ) {

      literal match {
        case Neg( t ) => negLiterals += t
        case _        => posLiterals += literal
      }

    }

    ( posLiterals.toSet, negLiterals.toSet )

  }

}

/**
 * Contains two sets to store integers
 * @param oneToMList Supposed to be a subset of {1,...,m}
 * @param oneToPList Supposed to be a subset of {1,...,p}
 */
class LeafIndex(
    val oneToMList: Set[Int],
    val oneToPList: Set[Int] ) {}

/**
 * Supposed to contain the data of a unified literal and whether it makes a non-tautological
 * leaf of the reduced representation true
 * @param literal
 * @param leafIndexList Supposed to contain the data which leaf of the reduced representation
 *                      becomes true for which substitution of the literal
 * @param numberOfDNTAs
 * @param foundNonEmptyPList Supposed to be true if there is a at least one leaf of the
 *                           reduced representation and one substitution of the
 *                           form (xCut->alpha,yCut->t_i(alpha)) such that the leaf becomes true
 * @param foundEmptyMList Supposed to be true if there is a at least one leaf of the
 *                        reduced representation and one substitution of the
 *                        form (xCut->r_j,yCut->beta_j) such that the leaf becomes true
 */
class LiteralWithIndexLists(
    val literal:            Formula,
    val leafIndexList:      List[LeafIndex],
    val numberOfDNTAs:      Int,
    val foundNonEmptyPList: Boolean,
    val foundEmptyMList:    Boolean ) {
  require( numberOfDNTAs == leafIndexList.length )
}

/**
 * Combined data of many unified literals in a clause and whether the clause is a
 * potential part of a formula in disjunctive normal form
 * that makes all leaves of the reduced representation true
 * @param literals
 */
class ClauseWithIndexLists(
    val literals: List[LiteralWithIndexLists] ) {

  require( literals.tail.forall( _.numberOfDNTAs == literals.head.numberOfDNTAs ) )

  def numberOfDNTAs: Int = this.literals.head.numberOfDNTAs

  /**
   * Computes an 'average' LeafIndex for the whole clause, i.e. the new oneToMList is
   * the union of all oneToMLists of each literal and the new
   * oneToPList is the intersection of all oneToPLists of each literal
   */
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
          leafIndexListClauseBufferP = leafIndexListClauseBufferP.intersect(
            literal.leafIndexList( leafNumber ).oneToPList )
        } )
        val leafIn = new LeafIndex( leafIndexListClauseBufferM, leafIndexListClauseBufferP )
        leafIndexListClauseBuffer = leafIndexListClauseBuffer :+ leafIn
      }
      leafIndexListClauseBuffer
    }
  }

  /**
   * Computes whether the clause is potentially a part of the cut formula
   */
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

  /**
   * Computes whether the supersets of the given clause have to be considered. True = supersets have to be considered
   */
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

  /**
   * Computes the formula that corresponds to the clause
   * @return
   */
  def formula: Formula = {

    var formulaBuffer: Formula = literals.head.literal
    literals.tail.foreach( literal => formulaBuffer = And( formulaBuffer, literal.literal ) )
    formulaBuffer
  }

}

/**
 * Combined data of many clauses in a set of clauses and whether the clauses translate
 * to a formula in disjunctive normal form
 * that makes all leaves of the reduced representation true
 * @param clauses
 */
class ClausesWithIndexLists(
    val clauses: List[ClauseWithIndexLists] ) {

  /**
   * Computes an 'average' LeafIndex for the whole set of clauses, i.e. the new oneToMList
   * is the intersection of all oneToMLists of each clause
   * and the new oneToPList is the union of all oneToPLists of each clause
   * @return
   */
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
            leafIndexListClausesBufferM = leafIndexListClausesBufferM.intersect(
              clause.leafIndexListClause( leafNumber ).oneToMList )
            leafIndexListClausesBufferP = leafIndexListClausesBufferP.union(
              clause.leafIndexListClause( leafNumber ).oneToPList )
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

  /**
   * Computes whether the set of clauses is a solution, i.e. the clauses translate to a formula in disjunctive normal form
   * that makes all leaves of the reduced representation true
   * @return
   */
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

  /**
   * Computes the formula that corresponds to the clauses
   * @return
   */
  def formula: Formula = {

    var formulaBuffer: Formula = this.clauses.head.formula
    this.clauses.tail.foreach( clause => formulaBuffer = Or( formulaBuffer, clause.formula ) )
    formulaBuffer
  }

}

/**
 * Computes the cut formula for a given schematic extended Herbrand sequent
 */
object introducePi2Cut {

  def apply(
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: Var     = fov"yCut",
    nameOfUniversalVariable:   Var     = fov"xCut" ): ( Option[Formula], Var, Var ) = {

    val nameOfExistentialVariableChecked =
      rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfExistentialVariable )
    val nameOfUniversalVariableChecked =
      rename.awayFrom( freeVariables( seHs.reducedRepresentationToFormula ) ).fresh( nameOfUniversalVariable )

    val unifiedLiterals: Set[Formula] = gStarUnify(
      seHs,
      nameOfExistentialVariableChecked,
      nameOfUniversalVariableChecked )

    val literalsWithIndexListsOrAndSolution: ( Set[LiteralWithIndexLists], Option[Formula] ) =
      computeTheIndexListsForTheLiterals(
        unifiedLiterals,
        seHs.dualNonTautologicalAxioms,
        seHs,
        nameOfExistentialVariableChecked,
        nameOfUniversalVariableChecked )

    val ( literalsWithIndexLists, optionSolution1 ) = literalsWithIndexListsOrAndSolution

    optionSolution1 match {
      case Some( t ) => return ( Some( t ), nameOfExistentialVariableChecked, nameOfUniversalVariableChecked )
      case None      =>
    }

    /// Only for additional data ///
    ////////////////////////////////
    var numberOfAllowedClauses: Option[Int] = None
    var numberOfCheckedFormulas: Int = literalsWithIndexLists.size
    ////////////////////////////////

    if ( literalsWithIndexLists.size > 1 ) {

      val allowedClausesWithIndexListsOrAndSolution: ( Set[ClauseWithIndexLists], Option[Formula] ) =
        checkAndBuildAllowedClausesHead(
          literalsWithIndexLists,
          seHs )

      val ( allowedClausesWithIndexLists, optionSolution2 ) = allowedClausesWithIndexListsOrAndSolution

      optionSolution2 match {
        case Some( t ) => return ( Some( t ), nameOfExistentialVariableChecked, nameOfUniversalVariableChecked )
        case None      =>
      }

      /// Only for additional data ///
      ////////////////////////////////
      numberOfAllowedClauses = Option( allowedClausesWithIndexLists.size )
      numberOfCheckedFormulas = allowedClausesWithIndexLists.size
      ////////////////////////////////

      for ( numberOfClauses <- 2 to allowedClausesWithIndexLists.size ) {
        for ( subset <- allowedClausesWithIndexLists.subsets( numberOfClauses ) ) {
          val clausesWithIndexLists = new ClausesWithIndexLists( subset.toList )
          if ( clausesWithIndexLists.isSolution ) {
            return (
              Option( clausesWithIndexLists.formula ),
              nameOfExistentialVariableChecked,
              nameOfUniversalVariableChecked )
          }

          /// Only for additional data ///
          ////////////////////////////////
          numberOfCheckedFormulas += 1
          ////////////////////////////////
        }
      }
    }

    /// Prints the most interesting data ///
    ////////////////////////////////////////

    /*
    println( "Number of non-tautological leaves" )
    println( seHs.dualNonTautologicalAxioms.length )
    println( "Non-tautological leaves" )
    println( seHs.dualNonTautologicalAxioms )
    println( "Substitution pairs alpha" )
    println( seHs.substitutionPairsAlpha )
    println( "Substitution pairs beta" )
    println( seHs.substitutionPairsBeta )
    println( "Number of unified literals" )
    println( unifiedLiterals.size )
    println( "Unified literals" )
    println( unifiedLiterals )
    numberOfAllowedClauses match {
      case Some( t ) => {
        println( "Number of allowed clauses" )
        println( t )
      }
      case None => println( "No 'allowed clauses' were computed" )
    }
    println( "Number of checked Formulas" )
    println( numberOfCheckedFormulas )
    */

    ( None, nameOfExistentialVariableChecked, nameOfUniversalVariableChecked )

  }

  private def checkAndBuildAllowedClausesHead(
    literalsWithIndexLists: Set[LiteralWithIndexLists],
    seHs:                   Pi2SeHs ): ( ( Set[ClauseWithIndexLists], Option[Formula] ) ) = {

    var allowedClausesWithIndexListsMutable = scala.collection.mutable.Set[ClauseWithIndexLists]()
    val literalsWithIndexListsMutable = scala.collection.mutable.Set( literalsWithIndexLists.toList: _* )

    for ( literalWithIndexLists <- literalsWithIndexLists ) {
      val clause = new ClauseWithIndexLists( List( literalWithIndexLists ) )
      val ( clauseIsUnnecessary, listOfUnnecessaryClauses ) =
        checkNecessityOfNewAndOldClause( clause, allowedClausesWithIndexListsMutable.toList )
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

    val ( mutable, optionSolution ) = checkAndBuildAllowedClauses(
      literalsWithIndexListsMutable,
      allowedClausesWithIndexListsMutable,
      seHs,
      2 )

    ( mutable.toSet, optionSolution )

  }

  private def checkAndBuildAllowedClauses(
    literalsWithIndexLists:       scala.collection.mutable.Set[LiteralWithIndexLists],
    allowedClausesWithIndexLists: scala.collection.mutable.Set[ClauseWithIndexLists],
    seHs:                         Pi2SeHs,
    subsetSize:                   Int ): ( ( scala.collection.mutable.Set[ClauseWithIndexLists], Option[Formula] ) ) = {

    for ( subset <- literalsWithIndexLists.subsets( subsetSize ) ) {
      val clauseWithIndexLists = new ClauseWithIndexLists( subset.toList )
      if ( clauseWithIndexLists.isAllowed ) {
        val ( clauseIsUnnecessary, listOfUnnecessaryClauses ) =
          checkNecessityOfNewAndOldClause( clauseWithIndexLists, allowedClausesWithIndexLists.toList )
        if ( !clauseIsUnnecessary ) {
          allowedClausesWithIndexLists += clauseWithIndexLists
          val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
          if ( clausesWithIndexLists.isSolution ) {
            return ( allowedClausesWithIndexLists, Option( clausesWithIndexLists.formula ) )
          }
          for ( unnecessaryClause <- listOfUnnecessaryClauses ) {
            allowedClausesWithIndexLists -= unnecessaryClause
          }
        }
        //      } else if ( !clauseWithIndexLists.isAllowedAtLeastAsSubformula ) {
        //        for ( literal <- subset ) {
        //          literalsWithIndexLists -= literal
        //        }
      }
    }

    if ( literalsWithIndexLists.size > subsetSize ) {
      checkAndBuildAllowedClauses(
        literalsWithIndexLists,
        allowedClausesWithIndexLists,
        seHs,
        subsetSize + 1 )
    } else {
      ( allowedClausesWithIndexLists, None )
    }

  }

  private def computeTheIndexListsForTheLiterals(
    unifiedLiterals:       Set[Formula],
    nonTautologicalLeaves: List[Sequent[Formula]],
    seHs:                  Pi2SeHs,
    y:                     Var,
    x:                     Var ): ( ( Set[LiteralWithIndexLists], Option[Formula] ) ) = {

    val literalWithIndexListsSet = scala.collection.mutable.Set[LiteralWithIndexLists]()

    for ( literal <- unifiedLiterals ) {

      var foundEmptyMOrPList: Boolean = false
      var foundNonEmptyPList: Boolean = false
      var foundEmptyMList: Boolean = false
      var leafOfIndexList: List[LeafIndex] = Nil

      val substitutedLiteralAsSequentListAlpha = for ( existsIndex <- 0 until seHs.multiplicityOfBeta )
        yield existsIndex -> ( Substitution(
        ( x, seHs.universalEigenvariable ),
        ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )( literal ) +: Sequent() )
      val substitutedLiteralAsSequentListBeta = for ( forallIndex <- 0 until seHs.multiplicityOfAlpha )
        yield forallIndex -> ( Neg( Substitution(
        ( x, seHs.substitutionsForAlpha( forallIndex ) ),
        ( y, seHs.existentialEigenvariables( forallIndex ) ) )( literal ) ) +: Sequent() )

      for ( leaf <- nonTautologicalLeaves ) {

        //var leafIndexP = Set[Int]()
        var leafIndexM = Set[Int]()

        /*
        for ( existsIndex <- 0 until seHs.multiplicityOfBeta ) {

          val subs = Substitution( ( x, seHs.universalEigenvariable ),
           ( y, seHs.substitutionsForBetaWithAlpha( existsIndex ) ) )
          val subsetSequent: Sequent[Formula] = subs( literal ).asInstanceOf[Formula] +: Sequent()
          if ( subsetSequent.isSubsetOf( leaf ) ) {
            leafIndexP += existsIndex
          }
        }
        */

        val leafIndexP: Set[Int] = substitutedLiteralAsSequentListAlpha.map( subsetSequent => {
          val ( index, sequent ) = subsetSequent
          if ( sequent.isSubsetOf( leaf ) ) {
            index
          } else {
            -1
          }
        } ).toSet.filter( i => i != -1 )

        for ( forallIndex <- 0 until seHs.multiplicityOfAlpha ) {

          val subs: Substitution = Substitution(
            ( x, seHs.substitutionsForAlpha( forallIndex ) ),
            ( y, seHs.existentialEigenvariables( forallIndex ) ) )
          val subsetSequent: Sequent[Formula] = Neg( subs( literal ) ) +: Sequent()
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
        foundEmptyMList )

      if ( foundNonEmptyPList ) {

        literalWithIndexListsSet += literalWithIndexLists

        if ( !foundEmptyMOrPList ) {
          val clauseWithIndexLists = new ClauseWithIndexLists( List( literalWithIndexLists ) )
          val clausesWithIndexLists = new ClausesWithIndexLists( List( clauseWithIndexLists ) )
          if ( clausesWithIndexLists.isSolution ) {
            return ( literalWithIndexListsSet.toSet, Option( clausesWithIndexLists.formula ) )
          }
        }
      }

    }

    ( literalWithIndexListsSet.toSet, None )

  }

  private def checkNecessityOfNewAndOldClause(
    newClause:  ClauseWithIndexLists,
    oldClauses: List[ClauseWithIndexLists] ): ( Boolean, List[ClauseWithIndexLists] ) = {

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
            if ( !newClause.leafIndexListClause( leafNumber ).oneToMList.subsetOf(
              oldClause.leafIndexListClause( leafNumber ).oneToMList ) ||
              !newClause.leafIndexListClause( leafNumber ).oneToPList.subsetOf(
                oldClause.leafIndexListClause( leafNumber ).oneToPList ) ) {
              clauseIsNotSubsetOfI( oldClauses.indexOf( oldClause ) ) = true
            }
          }

          if ( !iIsNotSubsetOfClause( oldClauses.indexOf( oldClause ) ) ) {
            if ( !oldClause.leafIndexListClause( leafNumber ).oneToMList.subsetOf(
              newClause.leafIndexListClause( leafNumber ).oneToMList ) ||
              !oldClause.leafIndexListClause( leafNumber ).oneToPList.subsetOf(
                newClause.leafIndexListClause( leafNumber ).oneToPList ) ) {
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