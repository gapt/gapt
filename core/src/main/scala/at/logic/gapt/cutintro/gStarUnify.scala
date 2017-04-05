package at.logic.gapt.cutintro
import at.logic.gapt.expr._

/**
 * Created by root on 26.01.17.
 */
object gStarUnify {

  /**
    * Computes the unified literals, i.e. the set of literals that are used to contruct the cut formula
    * @param seHs The given schematic Pi2-grammar
    * @param nameOfExistentialVariable Name of the existential variable of the cut-formula
    * @param nameOfUniversalVariable Name of the universal variable of the cut-formula
    * @return Set of unified literals
    */
  def apply(
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Set[FOLFormula] = {

    // To compute the unified literals, we have to consider all unification pairs.
    // These are pairs of literals (P,Q) occurring in the reduced representation such that:
    // The universal eigenvariable alpha may occurs in P but none of the existential eigenvariables beta_1,...,beta_m.
    // Some of the existential eigenvariables beta_1,...,beta_m may occur in Q but not the universal eigenvariable alpha.
    // Unification pairs are unifiable if there are terms s,t such that a replacement of terms in P by s and a replacement
    // of terms in Q by s turn the result into dual literals. Therefore, we can assume that exactly one literal is negated.
    // Note that the set itself indicates whether the literal is negated or not. The negation has already been dropped.
    val ( alpha, beta, neutral ) = seHs.literalsInTheDNTAs
    val ( alphaPos, alphaNeg ) = seHs.sortAndAtomize( alpha )
    val ( betaPos, betaNeg ) = seHs.sortAndAtomize( beta )
    val ( neutralPos, neutralNeg ) = seHs.sortAndAtomize( neutral )

    // Set that eventually becomes the return value, i.e. the set of unified literals
    val unifiedLiterals = scala.collection.mutable.Set[FOLFormula]()

    alphaPos.foreach( posAt =>
      betaNeg.union( neutralNeg ).foreach( negAt =>
        unifyLiterals(
          seHs,
          posAt,
          negAt,
          nameOfExistentialVariable,
          nameOfUniversalVariable
        ) match {
          case Some( t ) => {
            unifiedLiterals += t
          }
          case None =>
        } ) )

    alphaNeg.foreach( posAt =>
      betaPos.union( neutralNeg ).foreach( negAt =>
        unifyLiterals(
          seHs,
          posAt,
          negAt,
          nameOfExistentialVariable,
          nameOfUniversalVariable
        ) match {
          case Some( t ) => {
            unifiedLiterals += Neg( t )
          }
          case None =>
        } ) )

    betaPos.foreach( posAt =>
      neutralNeg.foreach( negAt =>
        unifyLiterals(
          seHs,
          posAt,
          negAt,
          nameOfExistentialVariable,
          nameOfUniversalVariable
        ) match {
          case Some( t ) => {
            unifiedLiterals += t
          }
          case None =>
        } ) )

    betaNeg.foreach( posAt =>
      neutralPos.foreach( negAt =>
        unifyLiterals(
          seHs,
          posAt,
          negAt,
          nameOfExistentialVariable,
          nameOfUniversalVariable
        ) match {
          case Some( t ) => {
            unifiedLiterals += Neg( t )
          }
          case None =>
        } ) )

    unifiedLiterals.toSet

  }

  /**
    * Checks whether the literals (only the names without the arguments) are dual to each other and calls
    * the unify function
    * @param seHs The given schematic Pi2-grammar
    * @param posAt First element of the unification pair
    * @param negAt Second element of the unification pair
    * @param nameOfExistentialVariable Name of the existential variable of the cut-formula
    * @param nameOfUniversalVariable Name of the universal variable of the cut-formula
    * @return Option type that might contain an unified literal, i.e. a literal in which neither the universal
    *         nor one of the existential eigenvariables occurs, but maybe nameOfExistentialVariable or nameOfUniversalVariable
    */
  private def unifyLiterals(
    seHs:                      Pi2SeHs,
    posAt:                     FOLFormula,
    negAt:                     FOLFormula,
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[FOLFormula] = {

    // nameOfPos and nameOfNeg are the names of the corresponding atoms that have to be equal. Otherwise, there is no unified literal.
    // In the case that the names are equal, we call the unify function with the arguments argsP and argsN of the corresponding literals.
    val Apps( nameOfPos, argsP ): FOLFormula = posAt
    val Apps( nameOfNeg, argsN ): FOLFormula = negAt

    val unifiedLiteral: Option[FOLFormula] = nameOfPos match {
      case t if ( ( nameOfNeg == t ) && ( argsP.length == argsN.length ) ) => {
        val unifiedArgs = unify(
          seHs,
          argsP.zip( argsN ),
          nameOfExistentialVariable,
          nameOfUniversalVariable
        )

        val theUnifiedLiteral = unifiedArgs match {
          case Some( s ) => {
            if ( s.length == argsP.length ) {
              Some( Apps( nameOfPos, s ).asInstanceOf[FOLFormula] )
            } else {
              None
            }
          }
          case _ => None
        }
        theUnifiedLiteral
      }
      case _ => None
    }

    unifiedLiteral

  }

  /**
    * Compares a zipped list of arguments and decides whether a pair of this list is unifiable corresponding to a
    * grammar seHs (see productionRules), whether we have to call the unify function on the subterms of the pair, or whether
    * the pair is not unifiable, i.e. whether to stop the whole function and return None
    * @param seHs The given schematic Pi2-grammar
    * @param zippedArgs Two lists of terms (Expr) that will be compared pairwise
    * @param nameOfExistentialVariable Name of the existential variable of the cut-formula
    * @param nameOfUniversalVariable Name of the universal variable of the cut-formula
    * @return An option type that might contain a list of terms (Expr) of the same length of zippedArgs in which neither the universal
    *         nor one of the existential eigenvariables occurs, but maybe nameOfExistentialVariable or nameOfUniversalVariable
    */
  private def unify(
    seHs:                      Pi2SeHs,
    zippedArgs:                List[( Expr, Expr )],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[Seq[FOLTerm]] = {

    var unifiedTerms: Option[Seq[FOLTerm]] = None
    // A boolean that is used to break the local loop
    var stopIt: Boolean = false
    // A boolean that is used to break the global loop
    var stopItAll: Boolean = false

    // A run through all pairs
    zippedArgs.foreach( t => {
      stopIt = false
      stopItAll = false

      // The current pair of terms (Expr) that is under consideration
      val ( tL, tR ) = t

      // If there are substitutions tL and tR for the universal variable of the cut formula then we can
      // replace tL or tR with nameOfUniversalVariable, i.e. we extend the current list of arguments with
      // nameOfUniversalVariable and stop the loop for the current pair of terms
      seHs.productionRulesXS.foreach( productionRuleX => if ( !stopIt ) {

        val ( productionRuleXL, productionRuleXR ) = productionRuleX

        if ( productionRuleXL.syntaxEquals( tL ) && productionRuleXR.syntaxEquals( tR ) ) {
          unifiedTerms = unifiedTerms match {
            case Some( update ) => Option( update :+ nameOfUniversalVariable )
            case None           => Option( Seq( nameOfUniversalVariable ) )
          }
          stopIt = true
          stopItAll = true
        }

      } )

      stopIt = false

      // If there are substitutions tL and tR for the existential variable of the cut formula then we can
      // replace tL or tR with nameOfExistentialVariable, i.e. we extend the current list of arguments with
      // nameOfExistentialVariable and stop the loop for the current pair of terms
      seHs.productionRulesYS.foreach( productionRuleY => if ( ( !stopIt ) && ( !stopItAll ) ) {

        val ( productionRuleYL, productionRuleYR ) = productionRuleY

        if ( productionRuleYL.syntaxEquals( tL ) && productionRuleYR.syntaxEquals( tR ) ) {
          unifiedTerms = unifiedTerms match {
            case Some( update ) => Option( update :+ nameOfExistentialVariable )
            case None           => Option( Seq( nameOfExistentialVariable ) )
          }
          stopIt = true
          stopItAll = true
        }

      } )

      if ( !stopItAll ) {

        // Since we could not unify the pair so far, we have to check whether the outermost function of the terms
        // is equal, whether the terms are equal, whether the terms are eigenvariables, or whether the pair is
        // not unifiable
        val Apps( nameOfArgL, argsOfArgL ) = tL
        val Apps( nameOfArgR, argsOfArgR ) = tR

        // If the terms are equal, we have to check whether the terms contain eigenvariables and replace them
        if ( tL.syntaxEquals( tR ) ) {

          var tLWasAEigenvariable: Boolean = false

          if ( tL.syntaxEquals( seHs.universalEigenvariable ) ) {

            tLWasAEigenvariable = true

            unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update :+ nameOfUniversalVariable )
              case None           => Option( Seq( nameOfUniversalVariable ) )
            }

          }

          seHs.existentialEigenvariables.foreach( existentialEigenvariable => if ( tL.syntaxEquals( existentialEigenvariable ) && !tLWasAEigenvariable ) {

            tLWasAEigenvariable = true

            unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update :+ nameOfExistentialVariable )
              case None           => Option( Seq( nameOfExistentialVariable ) )
            }

          } )

          if ( !tLWasAEigenvariable && ( argsOfArgL.length == 0 ) ) {

            tLWasAEigenvariable = true

            unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update :+ tL.asInstanceOf[FOLTerm] )
              case None           => Option( Seq( tR.asInstanceOf[FOLTerm] ) )
            }

          }

          if ( ( !tLWasAEigenvariable ) ) {

            unify(
              seHs,
              argsOfArgL.zip( argsOfArgR ),
              nameOfExistentialVariable,
              nameOfUniversalVariable
            ) match {
                case Some( r ) => unifiedTerms = unifiedTerms match {
                  case Some( update ) => Option( update :+ Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] )
                  case None           => Option( Seq( Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] ) )
                }
                case _ => unifiedTerms = None
              }

          }

        // If only the names of the outermost functions are equal we call the unify function on the arguments
        } else if ( ( nameOfArgL == nameOfArgR ) && ( argsOfArgL.length == argsOfArgR.length ) ) {

          unify(
            seHs,
            argsOfArgL.zip( argsOfArgR ),
            nameOfExistentialVariable,
            nameOfUniversalVariable
          ) match {
              case Some( r ) => unifiedTerms = unifiedTerms match {
                case Some( update ) => Option( update :+ Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] )
                case None           => Option( Seq( Apps( nameOfArgL, r ).asInstanceOf[FOLTerm] ) )
              }
              case _ => unifiedTerms = None
            }

        }
        // If the pair was not unified the list of arguments will be too short. Hence, the literals will not be unified.

      }

    } )

    unifiedTerms

  }

}
