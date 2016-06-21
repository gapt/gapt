package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.grammars.{ RecSchemTemplate, RecursionScheme, Rule }
import at.logic.gapt.proofs.lk.skolemize
import at.logic.gapt.proofs.{ Context, FiniteContext, HOLClause }
import at.logic.gapt.proofs.resolution.{ forgetfulPropParam, forgetfulPropResolve }
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.verit.VeriT

import scala.collection.mutable

case class MaxSatRecSchemFinder(
    paramTys:         Seq[Ty],
    pi1QTys:          Seq[TBase],
    instanceType:     Ty,
    grammarWeighting: Rule => Int,
    context:          FiniteContext
) extends InductiveGrammarFindingMethod {
  implicit def ctx = context

  val vs = for ( ( t, i ) <- paramTys.zipWithIndex ) yield Var( s"z$i", t )
  val A = Const( "A", FunctionType( instanceType, paramTys ) )
  val template = simplePi1RecSchemTempl( A( vs ), pi1QTys )

  def find( taggedLanguage: Set[( Seq[LambdaExpression], LambdaExpression )] ): RecursionScheme = {
    val targets = for ( ( ts, r ) <- taggedLanguage ) yield A( ts ) -> r
    template.findMinimalCoverViaInst( targets, weight = grammarWeighting )
  }
}

object simplePi1RecSchemTempl {
  def apply( axiom: LambdaExpression, pi1QTys: Seq[TBase] )( implicit ctx: FiniteContext ): RecSchemTemplate = {
    val nameGen = rename.awayFrom( ctx.constants )

    val Apps( axiomNT: Const, axiomArgs ) = axiom
    val FunctionType( instTT, axiomArgTys ) = axiomNT.exptype
    // TODO: handle strong quantifiers in conclusion correctly
    val axiomArgs2 = for ( ( t, i ) <- axiomArgTys.zipWithIndex ) yield Var( s"x_$i", t )

    val indLemmaNT = Const( nameGen fresh "B", FunctionType( instTT, axiomArgTys ++ axiomArgTys ++ pi1QTys ) )

    val lhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w_$i", t )
    val rhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"v_$i", t )

    val indLemmaRules = axiomArgTys.zipWithIndex.flatMap {
      case ( indLemmaArgTy: TBase, indLemmaArgIdx ) =>
        ctx.typeDef( indLemmaArgTy.name ).get match {
          case Context.Sort( _ ) => Seq()
          case Context.InductiveType( indTy, ctrs ) =>
            ctrs flatMap { ctr =>
              val FunctionType( _, ctrArgTys ) = ctr.exptype
              val ctrArgs = for ( ( t, i ) <- ctrArgTys.zipWithIndex ) yield Var( s"x_${indLemmaArgIdx}_$i", t )
              val lhs = indLemmaNT( axiomArgs: _* )( axiomArgs2.take( indLemmaArgIdx ): _* )( ctr( ctrArgs: _* ) )( axiomArgs2.drop( indLemmaArgIdx + 1 ): _* )( lhsPi1QArgs: _* )
              val recRules = ctrArgTys.zipWithIndex.filter { _._1 == indTy } map {
                case ( ctrArgTy, ctrArgIdx ) =>
                  lhs -> indLemmaNT( axiomArgs: _* )( axiomArgs2.take( indLemmaArgIdx ): _* )( ctrArgs( ctrArgIdx ) )( axiomArgs2.drop( indLemmaArgIdx + 1 ): _* )( rhsPi1QArgs: _* )
              }
              recRules :+ ( lhs -> Var( "u", instTT ) )
            }
        }
    }

    RecSchemTemplate(
      axiomNT,
      indLemmaRules.toSet
        + ( axiomNT( axiomArgs: _* ) -> indLemmaNT( axiomArgs: _* )( axiomArgs: _* )( rhsPi1QArgs: _* ) )
        + ( axiomNT( axiomArgs: _* ) -> Var( "u", instTT ) )
    //        + ( indLemmaNT( axiomArgs: _* )( lhsPi1QArgs: _* ) -> Var( "u", instTT ) )
    )
  }
}

object canonicalRsLHS {
  def apply( recSchem: RecursionScheme )( implicit ctx: Context ): Set[LambdaExpression] =
    recSchem.nonTerminals flatMap { nt =>
      val FunctionType( To, argTypes ) = nt.exptype
      val args = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x$i", t )
      recSchem.rulesFrom( nt ).flatMap {
        case Rule( Apps( _, as ), _ ) => as.zipWithIndex.filterNot { _._1.isInstanceOf[Var] }.map { _._2 }
      }.toSeq match {
        case Seq() => Some( nt( args: _* ) )
        case idcs =>
          val newArgs = for ( ( TBase( indTyName ), idx ) <- argTypes.zipWithIndex ) yield if ( !idcs.contains( idx ) ) List( args( idx ) )
          else {
            val TBase( indTyName ) = argTypes( idx )
            val Some( Context.InductiveType( indTy, ctrs ) ) = ctx.typeDef( indTyName )
            for {
              ctr <- ctrs.toList
              FunctionType( _, ctrArgTys ) = ctr.exptype
            } yield ctr(
              ( for ( ( t, i ) <- ctrArgTys.zipWithIndex ) yield Var( s"x${idx}_$i", t ) ): _*
            )
          }
          import scalaz._, Scalaz._
          newArgs.traverse( identity ).map( nt( _: _* ) ): List[LambdaExpression]
      }
    }
}

object homogenizeRS {
  def apply( recSchem: RecursionScheme )( implicit ctx: Context ): RecursionScheme = {
    val lhss = canonicalRsLHS( recSchem )
    val rules =
      for {
        lhs <- lhss
        r @ Rule( lhs_, rhs ) <- recSchem.rules
        subst <- syntacticMatching( lhs_, lhs )
      } yield subst( r )
    val terminalRHSs = rules collect { case Rule( _, rhs @ Apps( hd: Const, _ ) ) if !recSchem.nonTerminals( hd ) => rhs }
    val extraRules = for ( lhs <- lhss; rhs <- terminalRHSs if freeVariables( rhs ) subsetOf freeVariables( lhs ) ) yield Rule( lhs, rhs )
    recSchem.copy( rules = rules ++ extraRules )
  }
}

object qbupForRecSchem {
  def apply( recSchem: RecursionScheme )( implicit ctx: Context ): HOLFormula = {
    def convert( term: LambdaExpression ): HOLFormula = term match {
      case Apps( ax, _ ) if ax == recSchem.axiom => Bottom()
      case Apps( nt @ Const( name, ty ), args ) if recSchem.nonTerminals contains nt =>
        HOLAtom( Var( s"X_$name", ty )( args: _* ) )
      case Neg( formula ) => formula
      case formula        => -formula
    }

    val lhss = canonicalRsLHS( recSchem )

    existsclosure( And( for ( lhs <- lhss ) yield All.Block(
      freeVariables( lhs ) toSeq,
      formulaToSequent.pos( And( for {
        Rule( lhs_, rhs ) <- recSchem.rules
        subst <- syntacticMatching( lhs_, lhs )
      } yield convert( subst( rhs ) ) )
        --> convert( lhs ) ).toImplication
    ) ) )
  }
}

object hSolveQBUP {

  private def getConjuncts( f: HOLFormula ): Set[HOLFormula] = f match {
    case All( _, g )                                 => getConjuncts( g )
    case And( g1, g2 )                               => getConjuncts( g1 ) union getConjuncts( g2 )
    case _ if !containsQuantifierOnLogicalLevel( f ) => Set( f )
  }

  def findConseq( start: HOLFormula, cond: HOLFormula, Xinst: LambdaExpression, subst: Substitution, forgetOne: Boolean ): Set[HOLFormula] = {
    val isSolution = mutable.Map[Set[HOLClause], Boolean]()

    def checkSol( cnf: Set[HOLClause] ): Unit =
      if ( !isSolution.contains( cnf ) ) {
        val substCnfFormula = subst( And( cnf map { _.toDisjunction } ) )
        if ( VeriT isValid TermReplacement( cond, Map( Xinst -> substCnfFormula ) ) ) {
          isSolution( cnf ) = true
          forgetfulPropResolve( cnf ) foreach checkSol
          forgetfulPropParam( cnf ) foreach checkSol
          if ( forgetOne ) for ( c <- cnf ) checkSol( cnf - c )
        } else {
          isSolution( cnf ) = false
        }
      }

    checkSol( CNFp.toClauseList( start ).map { _.distinct.sortBy { _.hashCode } }.toSet )

    isSolution collect { case ( sol, true ) => And( sol map { _.toDisjunction } ) } toSet
  }

  def apply( qbupMatrix: HOLFormula, xInst: LambdaExpression, start: HOLFormula, forgetOne: Boolean ): Option[LambdaExpression] = {
    val Apps( x: Var, xInstArgs ) = xInst
    val conjuncts = getConjuncts( qbupMatrix )

    // FIXME: more than one condition
    val ( searchCondition, searchSubst ) = conjuncts flatMap { c =>
      val xOccs = subTerms( c ) collect { case occ @ Apps( `x`, args ) if args.size == xInstArgs.size => occ }
      // FIXME: two-sided mgu
      syntacticMGU( xOccs map { _ -> xInst } ) map { mgu =>
        mgu( c ) -> mgu
      }
    } head

    val conseqs = findConseq( start, searchCondition, searchSubst( xInst ), searchSubst, forgetOne )

    val xGenArgs = xInstArgs.zipWithIndex.map { case ( a, i ) => Var( s"x$i", a.exptype ) }
    val xGen = x( xGenArgs: _* )
    val Some( matching ) = syntacticMatching( xGen, xInst )
    conseqs foreach { conseq =>
      val genConseq = TermReplacement( conseq, matching.map.map( _.swap ) )
      val sol = Abs( xGenArgs, genConseq )
      if ( Z3 isValid skolemize( BetaReduction.betaNormalize( Substitution( x -> sol )( qbupMatrix ) ) ) ) {
        return Some( sol )
      }
    }
    None
  }

}
