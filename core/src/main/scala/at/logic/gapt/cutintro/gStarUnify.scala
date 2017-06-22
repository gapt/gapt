package at.logic.gapt.cutintro
import at.logic.gapt.expr._

/**
 * Computes the unified literals, i.e. the set of literals that are used to contruct the cut formula
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
    nameOfExistentialVariable: Var,
    nameOfUniversalVariable:   Var
  ): Set[Formula] = {

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
    ( for {
      ( alphas, betas ) <- Seq(
        alphaPos -> betaNeg, alphaPos -> neutralNeg,
        alphaNeg -> betaPos, alphaNeg -> neutralPos,
        neutralNeg -> betaPos, neutralPos -> betaNeg
      )
      posAt <- alphas
      negAt <- betas
      lit <- unifyLiterals( seHs, posAt, negAt, nameOfExistentialVariable, nameOfUniversalVariable )
    } yield lit ).toSet
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
    posAt:                     Formula,
    negAt:                     Formula,
    nameOfExistentialVariable: Var,
    nameOfUniversalVariable:   Var
  ): Option[Formula] = {

    // nameOfPos and nameOfNeg are the names of the corresponding atoms that have to be equal. Otherwise, there is no unified literal.
    // In the case that the names are equal, we call the unify function with the arguments argsP and argsN of the corresponding literals.
    val Apps( nameOfPos, argsP ): Formula = posAt
    val Apps( nameOfNeg, argsN ): Formula = negAt

    val unifiedLiteral: Option[Formula] = nameOfPos match {
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
              Some( Apps( nameOfPos, s ).asInstanceOf[Formula] )
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
    nameOfExistentialVariable: Var,
    nameOfUniversalVariable:   Var
  ): Option[Seq[Expr]] = {

    var unifiedTerms: Option[Seq[Expr]] = None

    // A run through all pairs
    zippedArgs.foreach( t => {

      unifiedTerms = unifiedTerms match {
        case Some( old ) => unifyPair( seHs, t, nameOfExistentialVariable, nameOfUniversalVariable ) match {
          case Some( update ) => Option( old :+ update )
          case None           => return None
        }
        case None => unifyPair( seHs, t, nameOfExistentialVariable, nameOfUniversalVariable ) match {
          case Some( update ) => Option( Seq( update ) )
          case None           => return None
        }
      }

    } )

    unifiedTerms

  }

  private def unifyPair(
    seHs:                      Pi2SeHs,
    termPair:                  ( Expr, Expr ),
    nameOfExistentialVariable: Var,
    nameOfUniversalVariable:   Var
  ): Option[Expr] = {

    // If there are substitutions tL and tR for the universal variable of the cut formula then we can
    // replace tL or tR with nameOfUniversalVariable, i.e. we extend the current list of arguments with
    // nameOfUniversalVariable and stop the loop for the current pair of terms
    unifyPairAccordingTo( seHs.productionRulesXS, termPair, nameOfUniversalVariable ) match {
      case Some( update ) => return Option( update )
      case None           =>
    }

    // If there are substitutions tL and tR for the existential variable of the cut formula then we can
    // replace tL or tR with nameOfExistentialVariable, i.e. we extend the current list of arguments with
    // nameOfExistentialVariable and stop the loop for the current pair of terms
    unifyPairAccordingTo( seHs.productionRulesYS, termPair, nameOfExistentialVariable ) match {
      case Some( update ) => return Option( update )
      case None           =>
    }

    // Since we could not unify the pair so far, we have to check whether the outermost function of the terms
    // is equal, whether the terms are equal, whether the terms are eigenvariables, or whether the pair is
    // not unifiable
    val ( tL, tR ) = termPair
    val Apps( nameOfArgL, argsOfArgL ) = tL
    val Apps( nameOfArgR, argsOfArgR ) = tR

    // If the terms are equal, we have to check whether the terms contain eigenvariables and replace them
    if ( ( nameOfArgL == nameOfArgR ) && ( argsOfArgL.length == argsOfArgR.length ) ) {

      if ( tL.syntaxEquals( seHs.universalEigenvariable ) ) return Option( nameOfUniversalVariable )

      seHs.existentialEigenvariables.foreach( existentialEigenvariable => if ( tL.syntaxEquals( existentialEigenvariable ) ) {
        return Option( nameOfExistentialVariable )
      } )

      if ( argsOfArgL.length == 0 ) return Some( tL )

      unify(
        seHs,
        argsOfArgL.zip( argsOfArgR ),
        nameOfExistentialVariable,
        nameOfUniversalVariable
      ) match {
          case Some( r ) => {
            if ( argsOfArgL.length == r.length ) return Some( Apps( nameOfArgL, r ) )
          }
          case None =>
        }

    }

    None
  }

  private def unifyPairAccordingTo(
    productionRules: List[( Expr, Expr )],
    termPair:        ( Expr, Expr ),
    name:            Var
  ): Option[Expr] =
    if ( productionRules contains termPair ) Some( name ) else None

}
