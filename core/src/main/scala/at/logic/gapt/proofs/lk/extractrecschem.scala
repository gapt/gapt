package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.{ Suc, Ant, SequentIndex, Sequent }

object extractRecSchem {
  def apply(
    p:                   LKProof,
    includeTheoryAxioms: Boolean = true,
    includeEqTheory:     Boolean = false
  ): RecursionScheme = {
    val symbols = p.endSequent.zipWithIndex map {
      case ( All.Block( vars, matrix ), Ant( _ ) ) => Abs( vars, matrix )
      case ( Ex.Block( vars, matrix ), Suc( _ ) )  => Abs( vars, -matrix )
    }
    val context = freeVariablesLK( p ).toList.sortBy( _.toString )
    val startSymbol = Const( "A", FunctionType( To, context.map( _.ty ) ) )
    RecursionScheme( startSymbol, new extractRecSchem( includeTheoryAxioms, includeEqTheory ).
      getRules(
        regularize( moveStrongQuantifierRulesDown( AtomicExpansion( p ) ) ),
        startSymbol( context: _* ), symbols.map( Some( _ ) ), context
      ) map {
          case Rule( lhs, rhs ) => Rule( lhs, BetaReduction.betaNormalize( rhs ) )
        } )
  }
}

private[lk] class extractRecSchem( includeTheoryAxioms: Boolean, includeEqTheory: Boolean ) {

  def symbolTypeP( f: Formula ): Ty = f match {
    case All( v, g )                   => v.ty -> symbolTypeP( g )
    case Ex( v, g )                    => ( v.ty -> symbolTypeN( g ) ) -> To
    case _ if !containsQuantifier( f ) => To
  }

  def symbolTypeN( f: Formula ): Ty = f match {
    case Ex( v, g )                    => v.ty -> symbolTypeN( g )
    case All( v, g )                   => ( v.ty -> symbolTypeP( g ) ) -> To
    case _ if !containsQuantifier( f ) => To
  }

  private val freshSymbols = Stream.from( 1 ).map( i => s"B$i" ).iterator
  private def mkFreshSymbol(): String = freshSymbols.next()

  private val freshVars = Stream.from( 1 ).map( i => s"X$i" ).iterator
  private def mkFreshVar(): String = freshVars.next()

  private object QuantifiedCut {
    def unapply( p: LKProof ) = p match {
      case CutRule( q1, aux1, q2, aux2 ) =>
        q1.conclusion( aux1 ) match {
          case All.Block( u, f ) if u.nonEmpty =>
            Some( ( q1, aux1, q2, aux2, true ) )
          case Ex.Block( u, f ) if u.nonEmpty =>
            Some( ( q2, aux2, q1, aux1, false ) )
          case _ => None
        }
      case _ => None
    }
  }

  private def findEigenVars( occ: SequentIndex, p: LKProof ): List[Var] = p match {
    case StrongQuantifierRule( subProof, aux, eigen, quant, pol ) if occ == p.mainIndices.head =>
      eigen :: findEigenVars( aux, subProof )
    case p @ InductionRule( _, _, _ ) if p.mainIndices contains occ =>
      findEigenVars( p.cases.head.conclusion, p.cases.head.proof )
    case p: ContractionRule if !p.mainIndices.contains( occ ) =>
      findEigenVars( p.getSequentConnector parent occ, p.subProof )
    case p: CutRule =>
      p.getLeftSequentConnector parents occ match {
        case Seq( pocc ) => findEigenVars( pocc, p.leftSubProof )
        case _ => p.getRightSequentConnector parents occ match {
          case Seq( pocc ) => findEigenVars( pocc, p.rightSubProof )
          case _           => throw new IllegalArgumentException
        }
      }
    case _ => Nil
  }

  private def allRules( symbols: Sequent[Option[Expr]], startSymbol: Expr ) =
    symbols.elements.flatten.map( Rule( startSymbol, _ ) ).toSet

  def getRules( p: LKProof, startSymbol: Expr, symbols: Sequent[Option[Expr]], context: List[Var] ): Set[Rule] = p match {
    case ReflexivityAxiom( term ) if includeEqTheory                                   => allRules( symbols, startSymbol ) + Rule( startSymbol, term === term )
    case ProofLink( _, sequent ) if includeTheoryAxioms                                => allRules( symbols, startSymbol ) + Rule( startSymbol, sequent.toImplication )
    case _: LogicalAxiom | _: ReflexivityAxiom | _: ProofLink | BottomAxiom | TopAxiom => allRules( symbols, startSymbol )
    case WeakQuantifierRule( q, aux, _, term, v, pol ) =>
      val main = p.mainIndices.head
      val appSym = App( symbols( main ).get, term )
      appSym.ty match {
        case FunctionType( To, argtypes ) -> To =>
          val eigenvars = findEigenVars( aux, q )
          val cpsSym = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.ty ) ++ argtypes ) ), context )
          val expCpsSym = Apps( cpsSym, eigenvars )
          expCpsSym.ty match {
            case To =>
              getRules( q, expCpsSym, p.occConnectors.head.parent( symbols ).updated( aux, None ), eigenvars ++ context ) +
                Rule( startSymbol, App( appSym, cpsSym ) )
            case nextCpsType -> To =>
              val nextCpsSym = Var( mkFreshVar(), nextCpsType )
              getRules( q, App( expCpsSym, nextCpsSym ), p.occConnectors.head.parent( symbols ).updated( aux, Some( nextCpsSym ) ), nextCpsSym :: eigenvars ++ context ) +
                Rule( startSymbol, App( appSym, cpsSym ) )
          }
        case _ =>
          getRules( q, startSymbol, p.occConnectors.head.parent( symbols ).updated( aux, Some( appSym ) ), context )
      }
    case QuantifiedCut( q1, aux1, q2, aux2, pol ) =>
      val symType = FunctionType( if ( pol ) symbolTypeP( q1.endSequent( aux1 ) ) else symbolTypeN( q1.endSequent( aux1 ) ), context.map( _.ty ) )
      val symbol = Apps( Const( mkFreshSymbol(), symType ), context )

      val occConn1 = p.occConnectors( if ( pol ) 0 else 1 )
      val occConn2 = p.occConnectors( if ( pol ) 1 else 0 )

      val eigenvars = findEigenVars( aux1, q1 )
      val hypSym = Apps( symbol, eigenvars )
      val rules1 = hypSym.ty match {
        case To => getRules( q1, hypSym, occConn1.parent( symbols, None ), eigenvars ++ context )
        case introType -> To =>
          val introSym = Var( mkFreshVar(), introType )
          val fullHypSym = App( hypSym, introSym )
          getRules( q1, fullHypSym, occConn1.parent( symbols, Some( introSym ) ), introSym :: eigenvars ++ context )
      }

      val rules2 = getRules( q2, startSymbol, occConn2.parent( symbols, Some( symbol ) ), context )
      rules1 ++ rules2
    case p @ InductionRule( cases, main, term ) =>
      val symbol = ( startSymbol, p.formula ) match {
        case ( Apps( Const( _, ty ), args ), Abs( _, All.Block( vs, _ ) ) ) =>
          Const( mkFreshSymbol(), ty )( args.dropRight( vs.size + 1 ) )
      }

      val caseRules = ( cases, p.occConnectors ).zipped flatMap { ( c, o ) =>
        val caseAxiom = symbol( c.constructor( c.eigenVars ) )( findEigenVars( c.conclusion, c.proof ) )

        var caseSymbols = o.parents( symbols ).map( _.head )
        ( c.hypotheses, c.hypVars ).zipped foreach { ( hyp, hypVar ) =>
          caseSymbols = caseSymbols.updated( hyp, Some( symbol( hypVar ) ) )
        }
        caseSymbols = caseSymbols.updated( c.conclusion, None ) // FIXME: pi2-induction

        getRules( c.proof, caseAxiom, caseSymbols, context ++ c.eigenVars )
      }

      caseRules.toSet + Rule( startSymbol, symbol( p.term )( findEigenVars( p.mainIndices.head, p ) ) )
    case p: EqualityRule if !includeEqTheory =>
      getRules( p.subProof, startSymbol, p.getSequentConnector parent symbols, context ) ++
        symbols( p.eqInConclusion ).map( Rule( startSymbol, _ ) )
    case p: EqualityLeftRule if includeEqTheory =>
      getRules( p.subProof, startSymbol, p.getSequentConnector parent symbols, context ) ++
        symbols( p.eqInConclusion ).map( Rule( startSymbol, _ ) ) +
        Rule( startSymbol, ( p.equation & p.mainFormula ) --> p.auxFormula )
    case p: EqualityRightRule if includeEqTheory =>
      getRules( p.subProof, startSymbol, p.getSequentConnector parent symbols, context ) ++
        symbols( p.eqInConclusion ).map( Rule( startSymbol, _ ) ) +
        Rule( startSymbol, ( p.equation & p.auxFormula ) --> p.mainFormula )
    case _ =>
      ( for (
        ( q, occConn ) <- p.immediateSubProofs zip p.occConnectors;
        rule <- getRules( q, startSymbol, occConn.parent( symbols, None ), context )
      ) yield rule ).toSet
  }
}