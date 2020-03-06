package gapt.logic.hol

import gapt.expr.formula.{ Formula, _ }
import gapt.expr.subst.Substitution
import gapt.expr.ty.{ FunctionType, To, Ty }
import gapt.expr.util.freeVariables
import gapt.expr.util.variables
import gapt.expr.{ Abs, BetaReduction, Expr, Var, VarOrConst }
import gapt.logic.Polarity
import gapt.proofs.HOLSequent
import gapt.provers.escargot.Escargot
import gapt.utils.NameGenerator
import gapt.utils.crossProduct

import scala.util.{ Failure, Success, Try }

/**
 * Uses the DLS algorithm to find a witness for formula equations of the form
 * ∃X_1 ... ∃X_n φ where φ is a first order formula and X_1,...,X_n are second-order variables.
 *
 * If the method succeeds, the return value is a tuple of a substitution of the second order variables in the
 * formula equation and a first order formula such that applying the substitution to the first-order formula
 * is a first-order formula which is equivalent to the given formula equation.
 *
 * A sufficient criterion for the success of the method in the case of formula equations of the form ∃X φ is that
 * φ can be put into the form
 *
 * (α_1(X) ∧ β_1(X)) ∨ ... ∨ (α_n(X) ∧ β_n(X))
 *
 * where
 * - no occurrences of X are inside the scope of a first-order existential quantifier,
 * - α_i(X) is positive with respect to X and β_i(X) is negative with respect to X and
 * - for every i either
 *   - α_i(X) does not contain X or
 *   - β_i(X) does not contain X or
 *   - every disjunction in α_i(X) ∧ β_i(X) contains at most one occurrence of X
 *
 * by
 * - simplifying φ,
 * - moving quantifiers as far down as possible to reduce their scope and
 * - distributing conjunctions over disjunctions in subformulae where positive and negative occurrences of X are not
 *   already separated by a conjunction.
 *
 * For formula equations with more than one variable the innermost formula equation is solved first,
 * then reduced to a first-order formula by applying the found substitution.
 * The method is then applied recursively on the resulting formula equation with one variable less.
 *
 * A Failure return value does not mean that the quantifier elimination is impossible.
 * It just means that this algorithm could not find a witness which allows elimination of the second order quantifier.
 * A Success return value does not mean that the returned first-order formula is valid, but only that it's equivalent
 * to the given formula equation.
 */
object dls {

  def apply( formula: Formula ): Try[( Substitution, Formula )] = Try( simplify( formula ) match {
    case Ex( StrictSecondOrderRelationVariable( x, _ ), innerFormula ) =>
      val ( s_, folPart ) = dls( innerFormula ).get
      val folInnerFormula = simplify( applySubstitutionBetaReduced( s_, folPart ) )
      val w = dls_( folInnerFormula, x )
      val s = updateSubstitutionWithBetaReduction( s_, x -> w )
      ( s, folPart )
    case f => ( Substitution(), f )
  } )

  private def dls_( f: Formula, X: Var ): Expr =
    findWitness( X, preprocess( X, f ) )

  def preprocess( X: Var, f: Formula ): Set[HOLSequent] = {
    separateConjuncts( X, extractDisjuncts( X, f ) ) match {
      case Left( inseparables ) =>
        throw new Exception(
          s"failed to separate positive and negative occurrences of ${X} in ${inseparables}" )
      case Right( separated ) => separated
    }
  }

  private def extractDisjuncts( X: Var, f: Formula ): Set[Formula] =
    toDisjuncts( moveQuantifiersInFormula( removeRedundantQuantifiers( toNNF( simplify( f ) ) ) ) )
      .filter( _.contains( X ) )

  private def separateConjuncts( X: Var, fs: Set[Formula] ): Either[Set[Formula], Set[HOLSequent]] = {
    val ( separable, inseparable ) = fs.partition( isSeparable( _, X ) )
    if ( inseparable.nonEmpty )
      Left( inseparable )
    else
      Right( separable.map( separateConjuncts( _, X ).get ) )
  }

  private def separateConjuncts( f: Formula, X: Var ): Option[HOLSequent] = {
    if ( !isSeparable( f, X ) )
      None
    else {
      val And.nAry( cs ) = f
      Some( HOLSequent( cs.map { c => c -> selectPolarity( c, X ).get } ) )
    }
  }

  private def isSeparable( d: Formula, X: Var ): Boolean = {
    val And.nAry( cs ) = d
    cs.forall( hasPolarity( X, _ ) )
  }

  private def hasPolarity( X: Var, f: Formula ): Boolean =
    occurrencePolarities( f, X ).size < 2

  private def selectPolarity( f: Formula, X: Var ): Option[Polarity] =
    occurrencePolarities( f, X ).toSeq match {
      case Seq()    => Some( Polarity.Positive )
      case Seq( p ) => Some( p )
      case _        => None
    }

  private def occurrencePolarities(
    formula:  Formula,
    variable: Var,
    polarity: Polarity = Polarity.Positive ): Set[Polarity] = formula match {
    case Atom( atomVariable, _ ) if atomVariable == variable => Set( polarity )
    case Neg( alpha ) =>
      occurrencePolarities( alpha, variable, !polarity )
    case AndOr( alpha, beta, _ ) =>
      occurrencePolarities( alpha, variable, polarity ) ++
        occurrencePolarities( beta, variable, polarity )
    case Quant( _, alpha, _ ) => occurrencePolarities( alpha, variable, polarity )
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
    val combinedWitness =
      if ( disjunctsWithWitnesses.size == 1 )
        disjunctsWithWitnesses.head._2
      else
        disjunctiveWitnessCombination( disjunctsWithWitnesses )

    Abs( variables, simplify( combinedWitness ) )
  }

  def findPartialWitness(
    secondOrderVariable: Var,
    argumentVariables:   List[Var],
    disjunct:            HOLSequent ): Formula = {
    val candidates = witnessCandidates( secondOrderVariable, argumentVariables, disjunct )
    val successfulCandidates = candidates.collect { case Success( w ) => w }
    val errors = candidates.collect { case Failure( e ) => e }
    if ( successfulCandidates.isEmpty ) {
      throw new Exception(
        s"cannot find witness for positive occurrences nor for negative occurrences " +
          s"in disjunct:\n$disjunct", errors.head )
    }
    simplify( chooseWitness( successfulCandidates ) )
  }

  private def witnessCandidates( X: Var, xs: Seq[Var], disjunct: HOLSequent ): Seq[Try[Formula]] =
    LazyList( positiveCandidate( X, xs, disjunct ), negativeCandidate( X, xs, disjunct ) )

  private def positiveCandidate( X: Var, xs: Seq[Var], disjunct: HOLSequent ): Try[Formula] =
    Try( polarityOccurrenceWitness.positive( X, xs, And( disjunct.succedent ) ) )

  private def negativeCandidate( X: Var, xs: Seq[Var], disjunct: HOLSequent ): Try[Formula] =
    Try( polarityOccurrenceWitness.negative( X, xs, And( disjunct.antecedent ) ) )

  private def chooseWitness( candidates: Seq[Formula] ): Formula = candidates.head

  private def moveQuantifiersInFormula( formula: Formula ): Formula = {
    moveQuantifiers.down( Ex, moveQuantifiers.down( All, formula ) )
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

  private def toDisjuncts( formula: Formula ): Set[Formula] = formula match {
    case And.nAry( conjuncts ) if conjuncts.length >= 2 =>
      crossProduct( conjuncts.map( toDisjuncts ) ).map( And( _ ) ).toSet

    case Or.nAry( disjuncts ) if disjuncts.length >= 2 =>
      disjuncts.flatMap( toDisjuncts ).toSet
    case _ => Set( formula )
  }

  /**
   * Simplify a formula using
   * - the equations for bottom and top,
   * - idempotence of conjunction and disjunction,
   * - absorption laws of conjunction and disjunction,
   * - commutativity and reflexivity of equality
   * - simple quantifier elimination (e.g. ∃x x = t ∧ φ(x) simplifies to φ[x/t])
   * - law of excluded middle and its dual and
   * - elimination of double negation.
   */
  def simplify( f: Formula ): Formula = toNNF( f ) match {
    case And.nAry( conjuncts ) if conjuncts.length >= 2 => simplifyMonoidalBinaryPropConnective( conjuncts, And, Or )
    case Or.nAry( disjuncts ) if disjuncts.length >= 2  => simplifyMonoidalBinaryPropConnective( disjuncts, Or, And )

    case Quant( x, innerFormula, isAll )                => simplifyQuantifier( x, innerFormula, isAll )

    case Neg( s ) => simplify( s ) match {
      case Top()      => Bottom()
      case Bottom()   => Top()
      case simplified => Neg( simplified )
    }
    case Eq( l, r ) if l == r               => Top()
    case Eq( l: VarOrConst, r: VarOrConst ) => Eq( List( l, r ).minBy( _.name ), List( l, r ).maxBy( _.name ) )
    case p                                  => p
  }

  private def simplifyMonoidalBinaryPropConnective(
    arguments:      List[Formula],
    connective:     MonoidalBinaryPropConnectiveHelper,
    dualConnective: MonoidalBinaryPropConnectiveHelper ): Formula = {
    val simplifiedArguments = arguments.map( simplify )
    val dualNeutral = dualConnective.neutral().asInstanceOf[Formula]
    if ( simplifiedArguments.contains( dualNeutral ) || containsPropAndItsNegation( simplifiedArguments ) )
      dualNeutral
    else {
      val neutralRemoved = simplifiedArguments.toSet.filterNot( _ == connective.neutral() )
      val absorbedRemoved = neutralRemoved.filterNot {
        case dualConnective.nAry( dualArguments ) if dualArguments.length >= 2 => dualArguments.exists( neutralRemoved.contains )
        case _ => false
      }
      connective( absorbedRemoved )
    }
  }

  private def simplifyQuantifier( variable: Var, innerFormula: Formula, isAll: Boolean ): Formula = {
    val simplificationConnective = if ( isAll ) Or else And
    val formula @ simplificationConnective.nAry( arguments ) = simplify( innerFormula )
    object UnaryPolarityConnective {
      def unapply( formula: Formula ): Option[Formula] = if ( isAll ) Neg.unapply( formula ) else Some( formula )
    }
    arguments.collectFirst {
      case UnaryPolarityConnective( Eq( lhs, rhs ) ) if lhs == variable || rhs == variable =>
        val substitute = if ( lhs == variable ) rhs else lhs
        val substitution = Substitution( variable -> substitute )
        simplify( BetaReduction.betaNormalize( substitution( simplificationConnective( arguments ) ) ) )
    }.getOrElse( formula match {
      case _ if !formula.contains( variable ) => formula
      case _                                  => Quant( variable, formula, isAll )
    } )
  }

  private def containsPropAndItsNegation( formulas: Seq[Formula] ): Boolean =
    formulas.exists( p => formulas.contains( simplify( Neg( p ) ) ) )

  private def freshArgumentVariables(
    secondOrderVariable: Var,
    disjuncts:           Set[HOLSequent] ): List[Var] = {
    val StrictSecondOrderRelationVariable( _, ( inputTypes, _ ) ) = secondOrderVariable
    val blackListVariableNames = disjuncts.flatMap( variables( _ ) ).map( _.name )
    val argumentName = secondOrderVariable.name.toLowerCase()
    new NameGenerator( blackListVariableNames )
      .freshStream( argumentName )
      .zip( inputTypes )
      .map { case ( name, inputType ) => Var( name, inputType ) }
      .toList
  }

  private object StrictSecondOrderRelationVariable {
    def unapply( variable: Var ): Option[( Var, ( Seq[Ty], Ty ) )] = variable match {
      case Var( _, FunctionType( To, inputTypes @ _ :: _ ) ) =>
        Some( ( variable, ( inputTypes, To ) ) )
      case _ => None
    }
  }

  private def updateSubstitutionWithBetaReduction( substitution: Substitution, entry: ( Var, Expr ) ): Substitution = {
    val newSubstitution = Substitution( entry )
    Substitution( newSubstitution.map ++ substitution.map.map( {
      case ( v, e ) => v -> ( e match {
        case Abs.Block( variables, f: Formula ) => Abs.Block( variables, simplify( applySubstitutionBetaReduced( newSubstitution, f ) ) )
      } )
    } ) )
  }

  private def applySubstitutionBetaReduced(
    substitution: Substitution,
    formula:      Formula ): Formula = {
    BetaReduction.betaNormalize( substitution( formula ) )
  }
}

object polarityOccurrenceWitness {

  def positive( x: Var, ys: Seq[Var], f: Formula ): Formula =
    polarityOccurrenceWitness( Polarity.Positive, x, ys, f )

  def negative( x: Var, ys: Seq[Var], f: Formula ): Formula =
    polarityOccurrenceWitness( Polarity.Negative, x, ys, f )

  /**
   * Returns the antecedent/succeedent (when given positive/negative polarity) of the implication in Ackermann's lemma
   * which is a witness for the given formula given that the formula has the respective polarity with respect to the
   * given second order variable
   */
  private def apply(
    polarity:            Polarity,
    secondOrderVariable: Var,
    argumentVariables:   Seq[Var],
    formula:             Formula ): Formula = {
    val polarityConnective = if ( polarity.positive ) Or else And
    val dualPolarityConnective = if ( polarity.positive ) And else Or
    val polarityQuantifier = if ( polarity.positive ) Ex else All
    val polarityInversion = if ( polarity.positive ) ( f: Formula ) => Neg( f ) else ( f: Formula ) => f
    val recur = polarityOccurrenceWitness( polarity, secondOrderVariable, argumentVariables, _ )
    formula match {
      case _ if !formula.contains( secondOrderVariable ) => polarityInversion( Top() )

      case Atom( variable, arguments ) if variable == secondOrderVariable =>
        vectorEq( argumentVariables, arguments )

      case Neg( Atom( variable, arguments ) ) if variable == secondOrderVariable =>
        Neg( vectorEq( argumentVariables, arguments ) )

      case And( alpha, beta ) =>
        polarityConnective(
          recur( alpha ),
          recur( beta ) )

      case Or.nAry( disjuncts ) if disjuncts.count( _.contains( secondOrderVariable ) ) >= 2 =>
        throw new Exception( "cannot handle disjunction of occurrences inside conjuncts" )

      case Or.nAry( disjuncts ) if disjuncts.length >= 2 =>
        val ( occurrenceDisjuncts, nonOccurrenceDisjuncts ) = disjuncts.partition( _.contains( secondOrderVariable ) )
        val occurrenceWitness = recur( occurrenceDisjuncts.head )
        dualPolarityConnective( occurrenceWitness, polarityInversion( Or( nonOccurrenceDisjuncts ) ) )

      case All( variable, innerFormula ) =>
        polarityQuantifier( variable, recur( innerFormula ) )

      case Ex( _, _ ) =>
        throw new Exception( "cannot handle occurrences inside the scope of existential quantifiers" )
    }
  }
}

object vectorEq {
  def apply( expressionsA: Iterable[Expr], expressionsB: Iterable[Expr] ): Formula = {
    And( expressionsA.zip( expressionsB ) map { case ( a, b ) => Eq( a, b ) } )
  }
}