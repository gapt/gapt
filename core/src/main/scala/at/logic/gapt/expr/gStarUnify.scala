package at.logic.gapt.expr

/**
 * Created by root on 26.01.17.
 */
object gStarUnify {

  def apply(
    setOfLiterals:             Set[FOLFormula],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    universalEigenvariable:    FOLVar,
    existentialEigenvariables: List[FOLVar],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Set[FOLFormula] = {

    val productionRulesXS: scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )] = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    productionRulesX.foreach( element => {
      productionRulesXS += element
      productionRulesXS += element.swap
    } )

    val productionRulesYS: scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )] = scala.collection.mutable.Set[( LambdaExpression, LambdaExpression )]()
    productionRulesY.foreach( element => {
      productionRulesYS += element
      productionRulesYS += element.swap
    } )

    val literals = sortAndAtomize( setOfLiterals )
    val ( posAtoms, negAtoms ) = literals

    val unifiedLiterals = scala.collection.mutable.Set[FOLFormula]()

    posAtoms.foreach( posAt =>
      negAtoms.foreach( negAt =>
        unifyLiterals(
          posAt,
          negAt,
          productionRulesXS.toSet,
          productionRulesYS.toSet,
          universalEigenvariable,
          existentialEigenvariables,
          nameOfExistentialVariable,
          nameOfUniversalVariable
        ) match {
          /*
          The next line is a compromise since we do not consider negation during the unification procedure (Future work). This way we add some unnecessary literals.
           */
          case Some( t ) => {
            unifiedLiterals += t
            unifiedLiterals += Neg( t )
          }
          case None =>
        } ) )

    unifiedLiterals.toSet

  }

  private def sortAndAtomize( literals: Set[FOLFormula] ): ( Set[FOLFormula], Set[FOLFormula] ) = {

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

  private def unifyLiterals(
    posAt:                     FOLFormula,
    negAt:                     FOLFormula,
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    universalEigenvariable:    FOLVar,
    existentialEigenvariables: List[FOLVar],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[FOLFormula] = {

    val Apps( nameOfPos, argsP ): FOLFormula = posAt
    val Apps( nameOfNeg, argsN ): FOLFormula = negAt

    val unifiedLiteral: Option[FOLFormula] = nameOfPos match {
      case t if ( ( nameOfNeg == t ) && ( argsP.length == argsN.length ) ) => {
        val unifiedArgs = unify(
          argsP.zip( argsN ),
          productionRulesX,
          productionRulesY,
          universalEigenvariable,
          existentialEigenvariables,
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

  private def unify(
    zippedArgs:                List[( LambdaExpression, LambdaExpression )],
    productionRulesX:          Set[( LambdaExpression, LambdaExpression )],
    productionRulesY:          Set[( LambdaExpression, LambdaExpression )],
    universalEigenvariable:    FOLVar,
    existentialEigenvariables: List[FOLVar],
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[Seq[FOLTerm]] = {

    var unifiedTerms: Option[Seq[FOLTerm]] = None
    var stopIt: Boolean = false
    var stopItAll: Boolean = false

    zippedArgs.foreach( t => {
      stopIt = false
      stopItAll = false

      val ( tL, tR ) = t

      productionRulesX.foreach( productionRuleX => if ( !stopIt ) {

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

      productionRulesY.foreach( productionRuleY => if ( ( !stopIt ) && ( !stopItAll ) ) {

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

        val Apps( nameOfArgL, argsOfArgL ) = tL
        val Apps( nameOfArgR, argsOfArgR ) = tR

        if ( tL.syntaxEquals( tR ) ) {

          var tLWasAEigenvariable: Boolean = false

          if ( tL.syntaxEquals( universalEigenvariable ) ) {

            tLWasAEigenvariable = true

            unifiedTerms = unifiedTerms match {
              case Some( update ) => Option( update :+ nameOfUniversalVariable )
              case None           => Option( Seq( nameOfUniversalVariable ) )
            }

          }

          existentialEigenvariables.foreach( existentialEigenvariable => if ( tL.syntaxEquals( existentialEigenvariable ) && !tLWasAEigenvariable ) {

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
              argsOfArgL.zip( argsOfArgR ),
              productionRulesX,
              productionRulesY,
              universalEigenvariable,
              existentialEigenvariables,
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

        } else if ( ( nameOfArgL == nameOfArgR ) && ( argsOfArgL.length == argsOfArgR.length ) ) {

          unify(
            argsOfArgL.zip( argsOfArgR ),
            productionRulesX,
            productionRulesY,
            universalEigenvariable,
            existentialEigenvariables,
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

      }

    } )

    unifiedTerms

  }

}
