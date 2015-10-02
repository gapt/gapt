package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence

object extractRecSchem {
  def apply( p: LKProof ): RecursionScheme = {
    val symbols = p.root.polarizedElements map {
      case ( occ, inAntecedent ) =>
        ( occ.formula, inAntecedent ) match {
          case ( All.Block( vars, matrix ), true ) => occ -> Abs( vars, matrix )
          case ( Ex.Block( vars, matrix ), false ) => occ -> Abs( vars, Neg( matrix ) )
        }
    }
    val context = freeVarsInProof( p ).toList.sortBy( _.toString )
    val axiom = Const( "A", FunctionType( To, context.map( _.exptype ) ) )
    RecursionScheme( axiom, getRules( p, axiom( context: _* ), symbols.toMap, context ) map {
      case Rule( lhs, rhs ) => Rule( lhs, BetaReduction.betaNormalize( rhs ) )
    } )
  }

  def freeVarsInProof( p: LKProof ): Set[Var] = freeVarsInProof( p, Set() )

  def freeVarsInProof( p: LKProof, bound: Set[Var] ): Set[Var] = ( p match {
    case StrongQuantifierRule( q, _, aux, main, eigenvar ) => freeVarsInProof( q, bound + eigenvar )
    case UnaryLKProof( rule, q, sequent, auxs, main ) => freeVarsInProof( q, bound )
    case BinaryLKProof( rule, q1, q2, sequent, aux1, aux2, main ) => freeVarsInProof( q1, bound ) ++ freeVarsInProof( q2, bound )
    case _ => Set()
  } ) ++ ( freeVariables( p.root.toFormula ) diff bound )

  def symbolTypeP( f: HOLFormula ): TA = f match {
    case All( v, g )                   => v.exptype -> symbolTypeP( g )
    case Ex( v, g )                    => ( v.exptype -> symbolTypeN( g ) ) -> To
    case _ if !containsQuantifier( f ) => To
  }

  def symbolTypeN( f: HOLFormula ): TA = f match {
    case Ex( v, g )                    => v.exptype -> symbolTypeN( g )
    case All( v, g )                   => ( v.exptype -> symbolTypeP( g ) ) -> To
    case _ if !containsQuantifier( f ) => To
  }

  private def followSymbols( symbols: Map[FormulaOccurrence, LambdaExpression], q: LKProof ) =
    for ( ( lowerOcc, sym ) <- symbols; occ <- q.root.occurrences if lowerOcc.isDescendantOf( occ, true ) )
      yield occ -> sym

  private val freshSymbols = Stream.from( 1 ).map( i => s"B$i" ).iterator
  private def mkFreshSymbol(): String = freshSymbols.next()

  private val freshVars = Stream.from( 1 ).map( i => s"X$i" ).iterator
  private def mkFreshVar(): String = freshVars.next()

  private object QuantifiedCut {
    def unapply( p: LKProof ) = p match {
      case CutRule( q1, q2, sequent, aux1, aux2 ) =>
        aux1.formula match {
          case All.Block( u, f ) if u.nonEmpty =>
            Some( ( q1, q2, sequent, aux1, aux2, aux1.formula, true ) )
          case Ex.Block( u, f ) if u.nonEmpty =>
            Some( ( q2, q1, sequent, aux2, aux1, aux1.formula, false ) )
          case _ => None
        }
      case _ => None
    }
  }

  private def findEigenVars( occ: FormulaOccurrence, p: LKProof ): List[Var] = p match {
    case StrongQuantifierRule( q, _, aux, main, eigenvar ) if main == occ =>
      eigenvar :: findEigenVars( aux, q )
    case InductionRule( q1, q2, sequent, base, stepl, stepr, main, term ) if main == occ =>
      findEigenVars( stepr, q2 ).map { case Var( s, t ) => Var( s"${s}_end", t ) } // hacky...
    case UnaryLKProof( rule, q, sequent, auxs, main ) if main != occ =>
      findEigenVars( q.root.occurrences.find( _.isAncestorOf( occ, false ) ).get, q )
    case BinaryLKProof( rule, q1, q2, sequent, aux1, aux2, main ) if !main.contains( occ ) =>
      Seq( q1, q2 ).
        flatMap { q => q.root.occurrences.find( _.isAncestorOf( occ, false ) ).map( findEigenVars( _, q ) ) }.
        maxBy( _.size )
    case _ => Nil
  }

  def getRules( p: LKProof, axiom: LambdaExpression, symbols: Map[FormulaOccurrence, LambdaExpression], context: List[Var] ): Set[Rule] = p match {
    case Axiom( sequent ) => sequent.occurrences.flatMap( symbols.get ).map { sym => Rule( axiom, sym ) } toSet
    case WeakQuantifierRule( q, _, aux, main, term ) =>
      val appSym = App( symbols( main ), term )
      appSym.exptype match {
        case FunctionType( To, argtypes ) -> To =>
          val eigenvars = findEigenVars( aux, q )
          val cpsSym = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ argtypes ) ), context )
          val expCpsSym = Apps( cpsSym, eigenvars )
          expCpsSym.exptype match {
            case To =>
              getRules( q, expCpsSym, followSymbols( symbols - main, q ), eigenvars ++ context ) +
                Rule( axiom, App( appSym, cpsSym ) )
            case nextCpsType -> To =>
              val nextCpsSym = Var( mkFreshVar(), nextCpsType )
              getRules( q, App( expCpsSym, nextCpsSym ), followSymbols( symbols - main, q ) + ( aux -> nextCpsSym ), nextCpsSym :: eigenvars ++ context ) +
                Rule( axiom, App( appSym, cpsSym ) )
          }
        case _ =>
          getRules( q, axiom, followSymbols( symbols - main, q ) + ( aux -> appSym ), context )
      }
    case QuantifiedCut( q1, q2, _, aux1, aux2, f, pol ) =>
      val symType = FunctionType( if ( pol ) symbolTypeP( f ) else symbolTypeN( f ), context.map( _.exptype ) )
      val symbol = Apps( Const( mkFreshSymbol(), symType ), context )

      val eigenvars = findEigenVars( aux1, q1 )
      val hypSym = Apps( symbol, eigenvars )
      val rules1 = hypSym.exptype match {
        case To => getRules( q1, hypSym, followSymbols( symbols, q1 ), eigenvars ++ context )
        case introType -> To =>
          val introSym = Var( mkFreshVar(), introType )
          val fullHypSym = App( hypSym, introSym )
          getRules( q1, fullHypSym, followSymbols( symbols, q1 ) + ( aux1 -> introSym ), introSym :: eigenvars ++ context )
      }

      val rules2 = getRules( q2, axiom, followSymbols( symbols, q2 ) + ( aux2 -> symbol ), context )
      rules1 ++ rules2
    case InductionRule( q1, q2, _, base, stepl, stepr, main, term ) =>
      val All.Block( vars, _ ) = stepl.formula.asInstanceOf[FOLFormula]
      val indVar = FOLMatchingAlgorithm.matchTerms( stepl.formula.asInstanceOf[FOLFormula], stepr.formula.asInstanceOf[FOLFormula] ).get.domain.head.asInstanceOf[FOLVar]
      val symbol = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ Seq( Ti ) ++ vars.map( _.exptype ) ) ), context )

      val baseAxiom = Apps( App( symbol, FOLConst( "0" ) ), findEigenVars( base, q1 ) )
      val rules1 = getRules( q1, baseAxiom, followSymbols( symbols - main, q1 ), context )

      val stepAxiom = Apps( App( symbol, FOLFunction( "s", indVar ) ), findEigenVars( stepr, q2 ) )
      val rules2 = getRules( q2, stepAxiom, followSymbols( symbols - main, q2 ) + ( stepl -> App( symbol, indVar ) ), indVar :: context )

      rules1 ++ rules2 + Rule( axiom, Apps( symbol, term :: findEigenVars( main, p ) ) )
    case BinaryLKProof( rule, q1, q2, _, aux1, aux2, main ) =>
      getRules( q1, axiom, followSymbols( symbols, q1 ), context ) ++ getRules( q2, axiom, followSymbols( symbols, q2 ), context )
    case UnaryLKProof( rule, q, _, auxs, main ) =>
      getRules( q, axiom, followSymbols( symbols, q ), context )
  }
}