package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
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
    val axiom = FOLFunction( "A" )
    RecursionScheme( getRules( p, axiom, symbols.toMap, List() ) )
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
      val rules1 = getRules( q1, axiom, followSymbols( symbols + ( aux1 -> symbol ), q1 ), context )
      val rules2 = getRules( q2, axiom, followSymbols( symbols + ( aux2 -> symbol ), q2 ), context )
      rules1 ++ rules2
    case BinaryLKProof( rule, q1, q2, sequent, aux1, aux2, main ) =>
      getRules( q1, axiom, followSymbols( symbols, q1 ), context ) ++ getRules( q2, axiom, followSymbols( symbols, q2 ), context )
    case UnaryLKProof( rule, q, sequent, auxs, main ) =>
      getRules( q, axiom, followSymbols( symbols, q ), context )
  }
}