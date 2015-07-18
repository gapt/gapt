package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

object extractRecSchem {
  def apply( p: LKProof ): RecursionScheme = {
    val encoding = new InstanceTermEncoding( p.root.toHOLSequent )
    val symbols =
      p.root.antecedent.map( occ => occ -> encoding.getSymbol( occ.formula.asInstanceOf[FOLFormula] -> true ) ) ++
        p.root.succedent.map( occ => occ -> encoding.getSymbol( occ.formula.asInstanceOf[FOLFormula] -> false ) )
    val context = freeVariables( p.root.toFormula.asInstanceOf[FOLFormula] ).toList
    val axiom = FOLFunction( "A", context )
    RecursionScheme( getRules( p, axiom, symbols.toMap, context ) )
  }

  private def followSymbols( symbols: Map[FormulaOccurrence, LambdaExpression], q: LKProof ) =
    for ( ( lowerOcc, sym ) <- symbols; occ <- q.root.occurrences if lowerOcc.isDescendantOf( occ, true ) )
      yield occ -> sym

  private val freshSymbols = Stream.from( 1 ).map( i => s"B$i" ).iterator
  private def mkFreshSymbol(): String = freshSymbols.next()

  def getRules( p: LKProof, axiom: FOLTerm, symbols: Map[FormulaOccurrence, LambdaExpression], context: List[FOLVar] ): Set[Rule] = p match {
    case Axiom( sequent ) => sequent.occurrences.flatMap( symbols.get ).map { sym => Rule( axiom, sym.asInstanceOf[FOLTerm] ) } toSet
    case ForallLeftRule( q, sequent, aux, main, term ) =>
      getRules( q, axiom,
        followSymbols( symbols - main, q )
          ++ symbols.get( main ).map { sym => aux -> App( sym, term ) },
        context )
    case ForallRightRule( q, sequent, aux, main, eigenvar: FOLVar ) =>
      App( symbols( main ), eigenvar ) match {
        case newAxiom: FOLTerm => getRules( q, newAxiom, followSymbols( symbols - main, q ), eigenvar :: context )
        case newSymbol         => getRules( q, axiom, followSymbols( symbols - main, q ) + ( aux -> newSymbol ), eigenvar :: context )
      }
    case CutRule( q1, q2, sequent, aux1, aux2 ) if containsQuantifier( aux1.formula ) =>
      val All.Block( vars, _ ) = aux1.formula
      val symbol = Apps( FOLFunctionHead( mkFreshSymbol(), context.size + vars.size ), context )
      val rules1 = getRules( q1, axiom, followSymbols( symbols, q1 ) + ( aux1 -> symbol ), context )
      val rules2 = getRules( q2, axiom, followSymbols( symbols, q2 ) + ( aux2 -> symbol ), context )
      rules1 ++ rules2
    case InductionRule( q1, q2, sequent, base, stepl, stepr, main, term ) =>
      val All.Block( vars, _ ) = stepl.formula.asInstanceOf[FOLFormula]
      val indVar = FOLMatchingAlgorithm.matchTerms( stepl.formula.asInstanceOf[FOLFormula], stepr.formula.asInstanceOf[FOLFormula] ).get.domain.head.asInstanceOf[FOLVar]
      val symbol = Apps( FOLFunctionHead( mkFreshSymbol(), context.size + 1 + vars.size ), context )
      val renaming = rename( vars.toSet, context.toSet )

      val baseAxiom = Apps( App( symbol, FOLConst( "0" ) ), vars map renaming ).asInstanceOf[FOLTerm]
      val rules1 = getRules( q1, baseAxiom, followSymbols( symbols - main, q1 ) + ( base -> App( symbol, FOLConst( "0" ) ) ), context )

      val stepAxiom = Apps( App( symbol, indVar ), vars map renaming ).asInstanceOf[FOLTerm]
      val rules2 = getRules( q2, stepAxiom, followSymbols( symbols - main, q2 ) + ( stepl -> App( symbol, indVar ) ) + ( stepr -> App( symbol, FOLFunction( "s", indVar ) ) ), indVar :: context )

      rules1 ++ rules2 + Rule( Apps( symbols( main ), vars ).asInstanceOf[FOLTerm], Apps( symbol, term :: vars ).asInstanceOf[FOLTerm] )
    case BinaryLKProof( rule, q1, q2, sequent, aux1, aux2, main ) =>
      getRules( q1, axiom, followSymbols( symbols, q1 ), context ) ++ getRules( q2, axiom, followSymbols( symbols, q2 ), context )
    case UnaryLKProof( rule, q, sequent, auxs, main ) =>
      getRules( q, axiom, followSymbols( symbols, q ), context )
  }
}