package at.logic.gapt.cutintro
import at.logic.gapt.expr._

/**
 * Created by root on 26.01.17.
 */
object gStarUnify {

  def apply(
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Set[FOLFormula] = {

    val literals = seHs.sortAndAtomize
    val ( posAtoms, negAtoms ) = literals

    val unifiedLiterals = scala.collection.mutable.Set[FOLFormula]()

    /*
    val unifiedLiteralsB: Set[FOLFormula] = for {
      posAt <- posAtoms
      negAt <- negAtoms
      lit <- unifyLiterals(
        seHs,
        posAt,
        negAt,
        nameOfExistentialVariable,
        nameOfUniversalVariable
      )
      litPosNeg <- Seq( lit, Neg( lit ) )
    } yield litPosNeg
    */

    posAtoms.foreach( posAt =>
      negAtoms.foreach( negAt =>
        unifyLiterals(
          seHs,
          posAt,
          negAt,
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

  private def unifyLiterals(
    seHs:                      Pi2SeHs,
    posAt:                     FOLFormula,
    negAt:                     FOLFormula,
    nameOfExistentialVariable: FOLVar,
    nameOfUniversalVariable:   FOLVar
  ): Option[FOLFormula] = {

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

  private def unify(
    seHs:                      Pi2SeHs,
    zippedArgs:                List[( LambdaExpression, LambdaExpression )],
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

        val Apps( nameOfArgL, argsOfArgL ) = tL
        val Apps( nameOfArgR, argsOfArgR ) = tR

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

      }

    } )

    unifiedTerms

  }

}
