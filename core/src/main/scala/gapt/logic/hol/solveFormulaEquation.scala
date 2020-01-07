package gapt.logic.hol

import gapt.expr.{Abs, BetaReduction, Expr, Var}
import gapt.expr.formula._
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.Substitution
import gapt.expr.ty.{FunctionType, Ti, To, Ty}
import gapt.expr.util.{freeVariables, rename, variables}
import gapt.logic.Polarity
import gapt.proofs.HOLSequent
import gapt.utils.NameGenerator

import scala.util.Try

object solveFormulaEquation {

  /**
   * Uses the DLS algorithm to find a witness for formula equations of the form
   * ?X_1 ... ?X_n φ where φ is a first order formula and X_1,...,X_n are second order variables.
   *
   * The return value is a substitution of the occurring second order variables such that
   * applying the substitution to φ gives a first order formula which is equivalent to
   * ?X_1 ... ?X_n φ.
   *
   * Does not yet work for formulas where a positive occurrence of the second order variable is
   * inside the scope of an existential quantifier which is itself inside the scope of an
   * universal quantifier.
   */
  def apply( formula: Formula ): Try[( Substitution, Formula )] = Try( formula match {
    case Ex( StrictSecondOrderVariable( secondOrderVariable, _ ), innerFormula ) =>
      val ( substitution, firstOrderPart ) = apply( innerFormula ).get
      val firstOrderFormula = applySubstitutionBetaReduced( substitution, firstOrderPart )
      val ( existentialVariables, disjuncts ) = preprocess( secondOrderVariable, firstOrderFormula )
      val witness = findWitness( secondOrderVariable, disjuncts )
      val substitutionMap = substitution.map + ( secondOrderVariable -> witness )
      val updatedSubstitution = Substitution( substitutionMap )
      val updatedInnerFormula = FirstOrderExBlock( existentialVariables, firstOrderFormula )
      ( updatedSubstitution, updatedInnerFormula )
    case _ => ( Substitution(), formula )
  } )

  private object StrictSecondOrderVariable {
    def unapply( variable: Var ): Option[( Var, ( Seq[Ty], Ty ) )] = variable match {
      case Var( _, FunctionType( To, inputTypes @ _ :: _ ) ) if inputTypes.forall( _ == Ti ) =>
        Some( ( variable, ( inputTypes, To ) ) )
      case _ => None
    }
  }

  private def applySubstitutionBetaReduced(
    substitution: Substitution,
    formula:      Formula ): Formula = {
    BetaReduction.betaNormalize( substitution( formula ) )
  }

  def preprocess(
    secondOrderVariable: Var,
    formula:             Formula ): ( List[FOLVar], Set[HOLSequent] ) = {
    val nnf = toNNF( formula )
    moveQuantifiers( nnf ) match {
      case FirstOrderExBlock( variables, innerFormula ) =>
        val disjuncts = distributeTopLevelConjunctionsOverDisjunctions( innerFormula )

        val polarizedConjunctsInDisjuncts = disjuncts
          .map( polarizedConjuncts( _, secondOrderVariable ) )
        if ( polarizedConjunctsInDisjuncts.exists( _.isEmpty ) )
          throw new Exception( "formula cannot be separated into positive and negative conjuncts" )
        else
          ( variables, polarizedConjunctsInDisjuncts.map( _.get ) )
    }
  }

  private def moveQuantifiers( formula: Formula ): Formula = {
    moveExistentialQuantifiersUp( moveUniversalQuantifiersDown( formula ) )
  }

  private def moveExistentialQuantifiersUp( formula: Formula ): Formula = formula match {
    case Or( Ex( variableAlpha, alpha ), Ex( variableBeta, beta ) ) =>
      val ( newVariable, substitutedFormulas ) = replaceVariablesWithNewVariable(
        List(
          ( variableAlpha, alpha ),
          ( variableBeta, beta ) ) )
      Ex( newVariable, moveExistentialQuantifiersUp( Or( substitutedFormulas ) ) )

    case AndOr( alpha, Ex( variable, beta ), connective ) =>
      val ( newVariable, substitutedFormulas ) = replaceVariablesWithNewVariable(
        List(
          ( variable, alpha ),
          ( variable, beta ) ) )
      Ex( newVariable, moveExistentialQuantifiersUp( connective( substitutedFormulas ) ) )

    case AndOr( Ex( variable, beta ), alpha, connective ) =>
      moveExistentialQuantifiersUp( connective( alpha, Ex( variable, beta ) ) )

    case Quant( variable, alpha, pol ) =>
      Quant( variable, moveExistentialQuantifiersUp( alpha ), pol )

    case AndOr( alpha, beta, connective ) =>
      val movedAlpha = moveExistentialQuantifiersUp( alpha )
      val movedBeta = moveExistentialQuantifiersUp( beta )
      if ( movedAlpha != alpha || movedBeta != beta )
        moveExistentialQuantifiersUp( connective( movedAlpha, movedBeta ) )
      else
        formula

    case _ => formula
  }

  private def replaceVariablesWithNewVariable[T](
    variablesInFormulas: Iterable[( Var, Formula )] ): ( Var, Iterable[Formula] ) =
    variablesInFormulas match {
      case ( headVariable: Var, _ ) :: _ =>
        val blackListVariables = variablesInFormulas.flatMap( x => variables( x._2 ) )
        val newVariable = rename( headVariable, blackListVariables )
        val substitute = Substitution( _: Var, newVariable )( _: Formula )
        ( newVariable, variablesInFormulas.map( x => substitute( x._1, x._2 ) ) )
    }

  private def moveUniversalQuantifiersDown( formula: Formula ): Formula = formula match {
    case All( variable, And( alpha, beta ) ) =>
      And(
        moveUniversalQuantifiersDown( All( variable, alpha ) ),
        moveUniversalQuantifiersDown( All( variable, beta ) ) )

    case All( variable, AndOr( alpha, beta, connective ) ) if !isFreeIn( variable, alpha ) =>
      connective(
        moveUniversalQuantifiersDown( alpha ),
        moveUniversalQuantifiersDown( All( variable, beta ) ) )

    case All( variable, AndOr( beta, alpha, connective ) ) if !isFreeIn( variable, alpha ) =>
      moveUniversalQuantifiersDown( All( variable, connective( alpha, beta ) ) )

    case Quant( variable, alpha, pol ) =>
      Quant( variable, moveUniversalQuantifiersDown( alpha ), pol )

    case AndOr( alpha, beta, connective ) =>
      connective(
        moveUniversalQuantifiersDown( alpha ),
        moveUniversalQuantifiersDown( beta ) )

    case _ => formula
  }

  private def isFreeIn( variable: Var, formula: Formula ): Boolean = {
    freeVariables( formula ).contains( variable )
  }

  private object AndOr {
    def unapply(
      formula: Formula ): Option[( Formula, Formula, MonoidalBinaryPropConnectiveHelper )] =
      formula match {
        case And( alpha, beta ) => Some( ( alpha, beta, And ) )
        case Or( alpha, beta )  => Some( ( alpha, beta, Or ) )
        case _                  => None
      }
  }

  private def distributeTopLevelConjunctionsOverDisjunctions(
    formula: Formula ): Set[Formula] = formula match {
    case And.nAry( conjuncts ) =>
      val disjunctsInConjuncts = conjuncts.map( { case Or.nAry( disjuncts ) => disjuncts } )
      crossProduct( disjunctsInConjuncts ).map( And.apply( _ ) ).toSet
  }

  private def crossProduct[T]( lists: Seq[Seq[T]] ): Seq[List[T]] = lists match {
    case Nil          => List( Nil )
    case head :: rest => for { x <- head; y <- crossProduct( rest ) } yield x :: y
  }

  private def polarizedConjuncts(
    formula:  Formula,
    variable: Var ): Option[HOLSequent] = formula match {
    case And.nAry( conjuncts ) =>
      val conjunctsWithPolarities = conjuncts
        .map( conjunct => ( conjunct, uniquePolarityWithRespectTo( conjunct, variable ) ) )

      if ( conjunctsWithPolarities.exists( { case ( _, polarity ) => polarity.isEmpty } ) )
        None
      else
        Some( HOLSequent( conjunctsWithPolarities.map( f => ( f._1, f._2.get ) ) ) )
  }

  private def uniquePolarityWithRespectTo( formula: Formula, variable: Var ): Option[Polarity] = {
    val polarities = polaritiesWithRespectTo( formula, variable )
    if ( polarities.size <= 1 )
      Some( polarities.headOption.getOrElse( Polarity.Positive ) )
    else
      None
  }

  private def polaritiesWithRespectTo(
    formula:  Formula,
    variable: Var,
    polarity: Polarity = Polarity.Positive ): Set[Polarity] = formula match {
    case Atom( atomVariable, _ ) if atomVariable == variable => Set( polarity )
    case Neg( alpha ) =>
      polaritiesWithRespectTo( alpha, variable, !polarity )
    case AndOr( alpha, beta, _ ) =>
      polaritiesWithRespectTo( alpha, variable, polarity ) ++
        polaritiesWithRespectTo( beta, variable, polarity )
    case Quant( _, alpha, _ ) => polaritiesWithRespectTo( alpha, variable, polarity )
    case _                    => Set()
  }

  private def findWitness( secondOrderVariable: Var, disjuncts: Set[HOLSequent] ): Expr = {
    val variables = freshArgumentVariables( secondOrderVariable, disjuncts )
    val disjunctsWithWitnesses = disjuncts.map(
      disjunct => {
        val witness = findPartialWitness( secondOrderVariable, variables, disjunct )
        val negativePart = And( disjunct.antecedent )
        val substitution = Substitution( secondOrderVariable -> Abs( variables, witness ) )
        ( applySubstitutionBetaReduced( substitution, negativePart ), witness )
      } )
    val witnessCombination = disjunctiveWitnessCombination( disjunctsWithWitnesses )
    Abs( variables, simplify( witnessCombination ) )
  }

  private def freshArgumentVariables(
    secondOrderVariable: Var,
    disjuncts:           Set[HOLSequent] ): List[FOLVar] = secondOrderVariable match {
    case StrictSecondOrderVariable( secondOrderVariable, ( inputTypes, _ ) ) =>
      val blackListVariableNames = disjuncts.flatMap( variables( _ ) ).map( _.name )
      val argumentName = secondOrderVariable.name.toLowerCase()
      new NameGenerator( blackListVariableNames )
        .freshStream( argumentName )
        .map( FOLVar( _ ) )
        .take( inputTypes.length )
        .toList
  }

  def findPartialWitness(
    secondOrderVariable: Var,
    argumentVariables:   List[FOLVar],
    disjunct:            HOLSequent ): Formula = {
    // todo: implement negativeOccurrencesWitness
    findPositiveOccurrencesWitness( secondOrderVariable, argumentVariables, disjunct )
  }

  private def findPositiveOccurrencesWitness(
    secondOrderVariable: Var,
    argumentVariables:   List[FOLVar],
    disjunct:            HOLSequent ): Formula = {
    val witness = positiveOccurrenceWitness(
      And( disjunct.succedent ),
      secondOrderVariable,
      argumentVariables )
    simplify( witness )
  }

  /**
   * Returns the succedent of the implication in Ackermann's lemma which is equivalent to the given
   * positive formula
   */
  private def positiveOccurrenceWitness(
    formula:             Formula,
    secondOrderVariable: Var,
    argumentVariables:   Seq[FOLVar] ): Formula = formula match {
    case _ if !formula.contains( secondOrderVariable ) => Top()
    case Atom( variable, arguments ) if variable == secondOrderVariable =>
      vectorEq( argumentVariables, arguments )
    case Neg( alpha ) =>
      Neg( positiveOccurrenceWitness( alpha, secondOrderVariable, argumentVariables ) )
    case And( alpha, beta ) =>
      Or(
        positiveOccurrenceWitness( alpha, secondOrderVariable, argumentVariables ),
        positiveOccurrenceWitness( beta, secondOrderVariable, argumentVariables ) )
    case Or.nAry( disjuncts ) if disjuncts.length >= 2 =>
      val partialWitnesses = disjuncts.map( disjunct => {
        val witness = positiveOccurrenceWitness(
          disjunct,
          secondOrderVariable,
          argumentVariables )
        val substitution = Substitution( secondOrderVariable, Abs( argumentVariables, witness ) )
        ( applySubstitutionBetaReduced( substitution, disjunct ), witness )
      } )
      disjunctiveWitnessCombination( partialWitnesses )
    case All( variable, innerFormula ) =>
      Ex( variable, positiveOccurrenceWitness( innerFormula, secondOrderVariable, argumentVariables ) )

    case Ex( _, _ ) =>
      throw new NotImplementedError( "cannot handle positive occurrences inside the scope of existential quantifiers yet" )

    // todo: handle Ex by skolemization
  }

  private def vectorEq( expressionsA: Iterable[Expr], expressionsB: Iterable[Expr] ): Formula = {
    And( expressionsA.zip( expressionsB ) map { case ( a, b ) => Eq( a, b ) } )
  }

  private def disjunctiveWitnessCombination(
    disjunctsWithWitnesses: Iterable[( Formula, Formula )] ): Formula = {
    And( disjunctsWithWitnesses.toList.inits.toList.init.map( initList => {
      val ( disjunct, witness ) = initList.last
      val negatedInit = initList.init.map( element => Neg( element._1 ) )
      val antecedent = And( negatedInit :+ disjunct )
      Imp( antecedent, witness )
    } ) )
  }

  private object FirstOrderExBlock {
    def apply( existentialVariables: List[FOLVar], formula: Formula ): Formula =
      existentialVariables match {
        case Nil              => formula
        case variable :: rest => Ex( variable, apply( rest, formula ) )
      }

    def unapply( formula: Formula ): Option[( List[FOLVar], Formula )] = formula match {
      case Ex( variable: FOLVar, innerFormula ) =>
        val ( variables, extractedFormula ) = unapply( innerFormula ).get
        Some( variable :: variables, extractedFormula )
      case _ => Some( Nil, formula )
    }
  }
}
