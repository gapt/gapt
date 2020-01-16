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
    val FirstOrderExBlock( variables, innerFormula ) = moveQuantifiersInFormula( nnf )
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
    case StrictSecondOrderRelationVariable( secondOrderVariable, ( inputTypes, _ ) ) =>
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

    // todo: handle Ex by skolemization
    case Ex( _, _ ) =>
      throw new NotImplementedError( "cannot handle positive occurrences inside the scope of existential quantifiers yet" )

    case _ if !formula.contains( secondOrderVariable ) => Top()
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