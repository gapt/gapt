package gapt.logic.hol

import gapt.expr.formula._
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.Substitution
import gapt.expr.ty.{ FunctionType, Ti, To, Ty }
import gapt.expr.util.variables
import gapt.expr.{ Abs, BetaReduction, Expr, Var }
import gapt.logic.Polarity
import gapt.proofs.HOLSequent
import gapt.utils.NameGenerator

import scala.util.{ Failure, Success, Try }

object solveFormulaEquation {

  /**
   * Uses the DLS algorithm to find a witness for formula equations of the form
   * ∃X_1 ... ∃X_n φ where φ is a first order formula and X_1,...,X_n are strict
   * second order variables.
   *
   * The return value is a tuple of a substitution of the second order variables in the formula equation
   * and a first order formula such that applying the substitution to the first order formula gives a
   * first order formula which is equivalent to ∃X_1 ... ∃X_n φ
   *
   * Does not yet work for formulas where an occurrence of the second order variable is
   * inside the scope of an existential quantifier which is itself inside the scope of an
   * universal quantifier.
   */
  def apply( formula: Formula ): Try[( Substitution, Formula )] = Try( formula match {
    case Ex( StrictSecondOrderRelationVariable( secondOrderVariable, _ ), innerFormula ) =>
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

  private object StrictSecondOrderRelationVariable {
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
    val formulaWithoutRedundantQuantifiers = removeRedundantQuantifiers( nnf )
    val FirstOrderExBlock( variables, innerFormula ) = moveQuantifiersInFormula( formulaWithoutRedundantQuantifiers )
    val disjuncts = distributeTopLevelConjunctionsOverDisjunctions( innerFormula )

    val polarizedConjunctsInDisjuncts = disjuncts
      .map( polarizedConjuncts( _, secondOrderVariable ) )
    if ( polarizedConjunctsInDisjuncts.exists( _.isEmpty ) )
      throw new Exception( "formula cannot be separated into positive and negative conjuncts" )
    else
      ( variables, polarizedConjunctsInDisjuncts.map( _.get ) )
  }

  private def moveQuantifiersInFormula( formula: Formula ): Formula = {
    moveQuantifiers.up( Ex, moveQuantifiers.down( All, formula ) )
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
    polarities.size match {
      case 0 => Some( Polarity.Positive )
      case 1 => polarities.headOption
      case _ => None
    }
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
        val negativePart = And( disjunct.antecedent ++ disjunct.succedent )
        val substitution = Substitution( secondOrderVariable -> Abs( variables, witness ) )
        ( applySubstitutionBetaReduced( substitution, negativePart ), witness )
      } )
    val witnessCombination = disjunctiveWitnessCombination( disjunctsWithWitnesses )
    Abs( variables, simplify( witnessCombination ) )
  }

  private def freshArgumentVariables(
    secondOrderVariable: Var,
    disjuncts:           Set[HOLSequent] ): List[FOLVar] = {
    val StrictSecondOrderRelationVariable( _, ( inputTypes, _ ) ) = secondOrderVariable
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
    val positiveOccurrenceWitness = Try( polarityOccurrenceWitness(
      Polarity.Positive,
      secondOrderVariable,
      argumentVariables,
      And( disjunct.succedent ) ) )
    val negativeOccurrenceWitness = Try( polarityOccurrenceWitness(
      Polarity.Negative,
      secondOrderVariable,
      argumentVariables,
      And( disjunct.antecedent ) ) )

    val witness = ( positiveOccurrenceWitness, negativeOccurrenceWitness ) match {
      case ( Success( positiveWitness ), Success( negativeWitness ) ) => chooseWitness( positiveWitness, negativeWitness )
      case ( Success( witness ), _ )                                  => witness
      case ( _, Success( witness ) )                                  => witness
      case ( Failure( exception ), _ )                                => throw new Exception( s"cannot find witness for positive occurrences nor for negative occurrences in disjunct:\n$disjunct", exception )
    }

    simplify( witness )
  }

  private def chooseWitness( positiveWitness: Formula, negativeWitness: Formula ): Formula = positiveWitness

  /**
   * Returns the antecedent/succeedent (when given positive/negative polarity) of the implication in Ackermann's lemma
   * which is a witness for the given formula given that the formula has the respective polarity with respect to the
   * given second order variable
   */
  private def polarityOccurrenceWitness(
    polarity:            Polarity,
    secondOrderVariable: Var,
    argumentVariables:   Seq[FOLVar],
    formula:             Formula ): Formula = {
    val polarityConnective = if ( polarity.positive ) Or else And
    val dualPolarityConnective = if ( polarity.positive ) And else Or
    val polarityQuantifier = if ( polarity.positive ) Ex else All
    val polarityInversion = if ( polarity.positive ) ( f: Formula ) => Neg( f ) else ( f: Formula ) => f
    val recur = polarityOccurrenceWitness( polarity, secondOrderVariable, argumentVariables, _ )
    formula match {
      case _ if !formula.contains( secondOrderVariable ) => polarityInversion( formula )

      case Atom( variable, arguments ) if variable == secondOrderVariable =>
        vectorEq( argumentVariables, arguments )

      case Neg( Atom( variable, arguments ) ) if variable == secondOrderVariable =>
        Neg( vectorEq( argumentVariables, arguments ) )

      case And( alpha, beta ) =>
        polarityConnective(
          recur( alpha ),
          recur( beta ) )

      case Or( alpha, beta ) =>
        dualPolarityConnective(
          recur( alpha ),
          recur( beta ) )

      case All( variable, innerFormula ) =>
        polarityQuantifier( variable, recur( innerFormula ) )

      case Ex( _, _ ) =>
        throw new Exception( "cannot handle occurrences inside the scope of existential quantifiers" )
    }
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