package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.{ Suc, Ant, SequentIndex, Sequent }

object extractRecSchem {
  def apply( p: at.logic.gapt.proofs.lk.base.LKProof ): RecursionScheme = apply( lkOld2New( p ) )

  def apply( p: LKProof ): RecursionScheme = {
    val symbols = p.endSequent.zipWithIndex map {
      case ( All.Block( vars, matrix ), Ant( _ ) ) => Abs( vars, matrix )
      case ( Ex.Block( vars, matrix ), Suc( _ ) )  => Abs( vars, Neg( matrix ) )
    }
    val context = freeVariablesLK( p ).toList.sortBy( _.toString )
    val axiom = Const( "A", FunctionType( To, context.map( _.exptype ) ) )
    RecursionScheme( axiom, getRules( regularize( moveStrongQuantifierRulesDown( p ) ), axiom( context: _* ), symbols, context ) map {
      case Rule( lhs, rhs ) => Rule( lhs, BetaReduction.betaNormalize( rhs ) )
    } )
  }

  def symbolTypeP( f: HOLFormula ): Ty = f match {
    case All( v, g )                   => v.exptype -> symbolTypeP( g )
    case Ex( v, g )                    => ( v.exptype -> symbolTypeN( g ) ) -> To
    case _ if !containsQuantifier( f ) => To
  }

  def symbolTypeN( f: HOLFormula ): Ty = f match {
    case Ex( v, g )                    => v.exptype -> symbolTypeN( g )
    case All( v, g )                   => ( v.exptype -> symbolTypeP( g ) ) -> To
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
    case InductionRule( q1, base, q2, stepl, stepr, term ) if occ == p.mainIndices.head =>
      findEigenVars( stepr, q2 ).map { case Var( s, t ) => Var( s"${s}_end", t ) } // hacky...
    case _ => Nil
  }

  def getRules( p: LKProof, axiom: LambdaExpression, symbols: Sequent[LambdaExpression], context: List[Var] ): Set[Rule] = p match {
    case _: InitialSequent => symbols.elements map { sym => Rule( axiom, sym ) } toSet
    case WeakQuantifierRule( q, aux, _, term, v, pol ) =>
      val main = p.mainIndices.head
      val appSym = App( symbols( main ), term )
      appSym.exptype match {
        case FunctionType( To, argtypes ) -> To =>
          val eigenvars = findEigenVars( aux, q )
          val cpsSym = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ argtypes ) ), context )
          val expCpsSym = Apps( cpsSym, eigenvars )
          expCpsSym.exptype match {
            case To =>
              getRules( q, expCpsSym, p.occConnectors.head.parents( symbols ).updated( aux, Seq( Top() ) ).map( _.head ), eigenvars ++ context ) +
                Rule( axiom, App( appSym, cpsSym ) )
            case nextCpsType -> To =>
              val nextCpsSym = Var( mkFreshVar(), nextCpsType )
              getRules( q, App( expCpsSym, nextCpsSym ), p.occConnectors.head.parents( symbols ).updated( aux, Seq( nextCpsSym ) ).map( _.head ), nextCpsSym :: eigenvars ++ context ) +
                Rule( axiom, App( appSym, cpsSym ) )
          }
        case _ =>
          getRules( q, axiom, p.occConnectors.head.parents( symbols ).updated( aux, Seq( appSym ) ).map( _.head ), context )
      }
    case QuantifiedCut( q1, aux1, q2, aux2, pol ) =>
      val symType = FunctionType( if ( pol ) symbolTypeP( q1.endSequent( aux1 ) ) else symbolTypeN( q1.endSequent( aux1 ) ), context.map( _.exptype ) )
      val symbol = Apps( Const( mkFreshSymbol(), symType ), context )

      val occConn1 = p.occConnectors( if ( pol ) 0 else 1 )
      val occConn2 = p.occConnectors( if ( pol ) 1 else 0 )

      val eigenvars = findEigenVars( aux1, q1 )
      val hypSym = Apps( symbol, eigenvars )
      val rules1 = hypSym.exptype match {
        case To => getRules( q1, hypSym, occConn1.parents( symbols ).map( _.headOption.getOrElse( Top() ) ), eigenvars ++ context )
        case introType -> To =>
          val introSym = Var( mkFreshVar(), introType )
          val fullHypSym = App( hypSym, introSym )
          getRules( q1, fullHypSym, occConn1.parents( symbols ).updated( aux1, Seq( introSym ) ).map( _.head ), introSym :: eigenvars ++ context )
      }

      val rules2 = getRules( q2, axiom, occConn2.parents( symbols ).updated( aux2, Seq( symbol ) ).map( _.head ), context )
      rules1 ++ rules2
    case p @ InductionRule( q1, base, q2, stepl, stepr, term ) =>
      val All.Block( vars, _ ) = q2.endSequent( stepl )
      val indVar = p.x
      val symbol = Apps( Const( mkFreshSymbol(), FunctionType( To, context.map( _.exptype ) ++ Seq( Ti ) ++ vars.map( _.exptype ) ) ), context )

      val baseAxiom = Apps( App( symbol, FOLConst( "0" ) ), findEigenVars( base, q1 ) )
      val rules1 = getRules( q1, baseAxiom, p.getLeftOccConnector.parents( symbols ).map( _.head ), context )

      val stepAxiom = Apps( App( symbol, FOLFunction( "s", indVar ) ), findEigenVars( stepr, q2 ) )
      val rules2 = getRules( q2, stepAxiom, p.getRightOccConnector.parents( symbols ).updated( stepl, Seq( App( symbol, indVar ) ) ).map( _.head ), indVar :: context )

      rules1 ++ rules2 + Rule( axiom, Apps( symbol, term :: findEigenVars( p.mainIndices.head, p ) ) )
    case _ =>
      ( for (
        ( q, occConn ) <- p.immediateSubProofs zip p.occConnectors;
        rule <- getRules( q, axiom, occConn.parents( symbols ).map( _.headOption.getOrElse( Top() ) ), context )
      ) yield rule ).toSet
  }
}