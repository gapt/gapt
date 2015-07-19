package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

object extractRecSchem {
  def apply( p: LKProof ): HORS = {
    val symbols = p.root.polarizedElements map {
      case ( occ, inAntecedent ) =>
        ( occ.formula, inAntecedent ) match {
          case ( All.Block( vars, matrix ), true ) => occ -> Abs( vars, matrix )
          case ( Ex.Block( vars, matrix ), false ) => occ -> Abs( vars, Neg( matrix ) )
        }
    }
    val context = freeVariables( p.root.toFormula.asInstanceOf[FOLFormula] ).toList
    val axiom = Apps( Const( "A", FunctionType( To, context.map( _.exptype ) ) ), context )
    HORS( getRules( p, axiom, symbols.toMap, context ) map {
      case HORule( lhs, rhs ) => HORule( lhs, BetaReduction.betaNormalize( rhs ) )
    } )
  }

  private def followSymbols( symbols: Map[FormulaOccurrence, LambdaExpression], q: LKProof ) =
    for ( ( lowerOcc, sym ) <- symbols; occ <- q.root.occurrences if lowerOcc.isDescendantOf( occ, true ) )
      yield occ -> sym

  private val freshSymbols = Stream.from( 1 ).map( i => s"B$i" ).iterator
  private def mkFreshSymbol(): String = freshSymbols.next()

  def getRules( p: LKProof, axiom: LambdaExpression, symbols: Map[FormulaOccurrence, LambdaExpression], context: List[Var] ): Set[HORule] = p match {
    case Axiom( sequent ) => sequent.occurrences.flatMap( symbols.get ).map { sym => HORule( axiom, sym ) } toSet
    case WeakQuantifierRule( q, sequent, aux, main, term ) =>
      val appSym = App( symbols( main ), term )
      appSym.exptype match {
        case FunctionType( To, argtypes ) -> To =>
          val cpsSym = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ argtypes ) ), context )
          getRules( q, axiom, followSymbols( symbols - main, q ) + ( aux -> cpsSym ), context ) +
            HORule( axiom, App( appSym, cpsSym ) )
        case _ =>
          getRules( q, axiom, followSymbols( symbols - main, q ) + ( aux -> appSym ), context )
      }
    case StrongQuantifierRule( q, sequent, aux, main, eigenvar: FOLVar ) =>
      val appSym = App( symbols( main ), eigenvar )
      appSym.exptype match {
        case FunctionType( To, argtypes ) -> To =>
          val introSym = Var( mkFreshSymbol(), FunctionType( To, argtypes ) )
          val fullyAppSym = App( appSym, introSym )
          getRules( q, fullyAppSym, followSymbols( symbols - main, q ) + ( aux -> introSym ), introSym :: eigenvar :: context )
        case To => getRules( q, appSym, followSymbols( symbols - main, q ), eigenvar :: context )
        case _  => getRules( q, axiom, followSymbols( symbols - main, q ) + ( aux -> appSym ), eigenvar :: context )
      }
    case CutRule( q1, q2, sequent, aux1, aux2 ) if containsQuantifier( aux1.formula ) =>
      val All.Block( u, Ex.Block( v, _ ) ) = aux1.formula
      val symType = if ( v.isEmpty )
        FunctionType( To, context.map( _.exptype ) ++ u.map( _.exptype ) )
      else FunctionType( To, context.map( _.exptype ) ++ u.map( _.exptype ) :+ FunctionType( To, v.map( _.exptype ) ) )
      val symbol = Apps( Const( mkFreshSymbol(), symType ), context )
      val rules1 = getRules( q1, axiom, followSymbols( symbols, q1 ) + ( aux1 -> symbol ), context )
      val rules2 = getRules( q2, axiom, followSymbols( symbols, q2 ) + ( aux2 -> symbol ), context )
      rules1 ++ rules2
    case InductionRule( q1, q2, sequent, base, stepl, stepr, main, term ) =>
      val All.Block( vars, _ ) = stepl.formula.asInstanceOf[FOLFormula]
      val indVar = FOLMatchingAlgorithm.matchTerms( stepl.formula.asInstanceOf[FOLFormula], stepr.formula.asInstanceOf[FOLFormula] ).get.domain.head.asInstanceOf[FOLVar]
      val symbol = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ Seq( Ti ) ++ vars.map( _.exptype ) ) ), context )
      val renaming = rename( vars.toSet, context.map( _.asInstanceOf[FOLVar] ).toSet )

      val baseAxiom = Apps( App( symbol, FOLConst( "0" ) ), vars map renaming )
      val rules1 = getRules( q1, baseAxiom, followSymbols( symbols - main, q1 ) + ( base -> App( symbol, FOLConst( "0" ) ) ), context )

      val stepAxiom = Apps( App( symbol, indVar ), vars map renaming )
      val rules2 = getRules( q2, stepAxiom, followSymbols( symbols - main, q2 ) + ( stepl -> App( symbol, indVar ) ) + ( stepr -> App( symbol, FOLFunction( "s", indVar ) ) ), indVar :: context )

      rules1 ++ rules2 + HORule( Apps( symbols( main ), vars ), Apps( symbol, term :: vars ) )
    case BinaryLKProof( rule, q1, q2, sequent, aux1, aux2, main ) =>
      getRules( q1, axiom, followSymbols( symbols, q1 ), context ) ++ getRules( q2, axiom, followSymbols( symbols, q2 ), context )
    case UnaryLKProof( rule, q, sequent, auxs, main ) =>
      getRules( q, axiom, followSymbols( symbols, q ), context )
  }
}