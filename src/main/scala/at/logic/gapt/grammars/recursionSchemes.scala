package at.logic.gapt.grammars

import at.logic.gapt.expr.fol.{ FOLUnificationAlgorithm, Numeral, FOLSubstitution, FOLMatchingAlgorithm }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ toNNF, simplify, lcomp }
import at.logic.gapt.provers.maxsat.{ QMaxSAT, MaxSATSolver }
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

case class Rule( lhs: FOLTerm, rhs: FOLTerm ) {
  require( freeVariables( rhs ) subsetOf freeVariables( lhs ) )

  def apply( term: FOLTerm ): Option[FOLTerm] =
    FOLMatchingAlgorithm.matchTerms( lhs, term ).map( _( rhs ) )

  def apply( subst: FOLSubstitution ): Rule =
    Rule( subst( lhs ), subst( rhs ) )

  override def toString: String =
    s"$lhs -> $rhs"
}

case class RecursionScheme( rules: Set[Rule] ) {
  def language( from: FOLTerm ): Set[FOLTerm] =
    rules flatMap ( _( from ) ) match {
      case irreducible if irreducible.isEmpty => Set( from )
      case oneStepReductions                  => oneStepReductions flatMap language
    }

  override def toString: String = rules.toSeq.sortBy( _.toString ) mkString "\n"
}

object preOrderTraversal {
  def apply( term: FOLTerm ): Seq[FOLTerm] = term match {
    case FOLFunction( _, as ) => term +: ( as flatMap apply )
    case FOLVar( _ )          => Seq( term )
  }
}

object canonicalVars {
  def apply( term: FOLTerm ): FOLTerm =
    FOLSubstitution( preOrderTraversal( term ).
      collect { case v: FOLVar => v }.
      distinct.
      zipWithIndex.map { case ( v, i ) => v -> FOLVar( s"x$i" ) } )( term )
}

object TargetFilter {
  type Type = ( FOLTerm, FOLTerm ) => Option[Boolean]

  def default: Type = ( from: FOLTerm, to: FOLTerm ) =>
    FOLMatchingAlgorithm.matchTerms( to, from ) match {
      case Some( _ ) => Some( true )
      case _         => None
    }
}

class RecSchemGenLangFormula( val recursionScheme: RecursionScheme,
                              val targetFilter: TargetFilter.Type = TargetFilter.default ) {

  def ruleIncluded( rule: Rule ) = FOLAtom( s"${rule.lhs}->${rule.rhs}" )
  def derivable( from: FOLTerm, to: FOLTerm ) = FOLAtom( s"$from=>$to" )

  def reverseMatch( rule: Rule, against: FOLTerm ) = {
    val rule_ = rule( FOLSubstitution( rename( freeVariables( rule.lhs ), freeVariables( against ) ) ) )
    FOLUnificationAlgorithm.unify( rule_.rhs, against ).headOption.map( _( rule_.lhs ) )
  }

  def apply( targets: Seq[( FOLTerm, FOLTerm )] ): FOLFormula = {
    val queue = mutable.Queue( targets: _* )
    val alreadyDone = mutable.Set[( FOLTerm, FOLTerm )]()
    val formulas = mutable.ListBuffer[FOLFormula]()

    targets foreach { case ( from, to ) => formulas += derivable( from, to ) }

    while ( queue nonEmpty ) {
      val target @ ( from, to ) = queue.dequeue()

      if ( !alreadyDone( target ) && FOLMatchingAlgorithm.matchTerms( to, from ).isEmpty ) {
        val possibleReductions = recursionScheme.rules flatMap { rule =>
          reverseMatch( rule, to ).map( canonicalVars( _ ) -> rule )
        }

        formulas += Imp( derivable( from, to ), Or( possibleReductions.toSeq flatMap {
          case ( newTo, rule ) =>
            targetFilter( from, newTo ) match {
              case Some( true ) =>
                Some( ruleIncluded( rule ) )
              case Some( false ) =>
                None
              case _ =>
                queue enqueue ( from -> newTo )
                Some( And( derivable( from, newTo ), ruleIncluded( rule ) ) )
            }
        } ) )
      }

      alreadyDone += target
    }

    And( formulas )
  }
}

object minimizeRecursionScheme extends Logger {
  def apply( recSchem: RecursionScheme, targets: Seq[( FOLTerm, FOLTerm )],
             targetFilter: TargetFilter.Type = TargetFilter.default,
             solver: MaxSATSolver = new QMaxSAT ) = {
    val formula = new RecSchemGenLangFormula( recSchem, targetFilter )
    val hard = formula( targets )
    warn( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> 1 }
    val interp = solver.solveWPM( List( hard ), soft toList ).get
    RecursionScheme( recSchem.rules.filter { rule => interp.interpret( formula.ruleIncluded( rule ) ) } )
  }
}

object SipRecSchem {

  val A = "A"
  val G = "G"

  def targetFilter: TargetFilter.Type =
    ( from: FOLTerm, to: FOLTerm ) =>
      TargetFilter.default( from, to ).orElse {
        from match {
          case FOLFunction( A, List( Numeral( n ) ) ) =>
            to match {
              case FOLFunction( G, List( x, _, _ ) ) if termSize( x ) > n + 1 => Some( false )
              case _ => None
            }
        }
      }

  def toSipGrammar( recSchem: RecursionScheme ) =
    SipGrammar( recSchem.rules.toSeq map {
      case Rule( FOLFunction( A, List( x: FOLVar ) ), FOLFunction( G, List( x_, u, x__ ) ) ) if x == x_ && x == x__ =>
        SipGrammar.gammaEnd -> FOLSubstitution( x -> SipGrammar.alpha )( u )
      case Rule( FOLFunction( A, List( x: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( x -> SipGrammar.alpha )( r )
      case Rule( FOLFunction( G, List( FOLFunction( "s", List( x: FOLVar ) ), y: FOLVar, z: FOLVar ) ), FOLFunction( G, List( x_, t, z_ ) ) ) if x == x_ && z == z_ =>
        SipGrammar.gamma -> FOLSubstitution( x -> SipGrammar.nu, y -> SipGrammar.gamma, z -> SipGrammar.alpha )( t )
      case Rule( FOLFunction( G, List( FOLFunction( "s", List( x: FOLVar ) ), y: FOLVar, z: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( x -> SipGrammar.nu, y -> SipGrammar.gamma, z -> SipGrammar.alpha )( r )
      case Rule( FOLFunction( G, List( FOLFunction( "0", List() ), y: FOLVar, z: FOLVar ) ), r ) =>
        SipGrammar.tau -> FOLSubstitution( y -> SipGrammar.beta, z -> SipGrammar.alpha )( r )
    } )

  def toTargets( instanceLanguages: Seq[normalFormsSipGrammar.InstanceLanguage] ) =
    instanceLanguages flatMap {
      case ( n, l ) =>
        l map ( FOLFunction( A, Numeral( n ) ) -> _ )
    }

  def normalForms( instanceLanguages: Seq[normalFormsSipGrammar.InstanceLanguage] ) = {
    val rules = Set.newBuilder[Rule]

    val Seq( x, y, z ) = Seq( "x", "y", "z" ).map( FOLVar( _ ) )
    val nfs = tratNormalForms( instanceLanguages flatMap ( _._2 ), Seq( x, y, z ) )
    for ( nf <- nfs ) {
      val fvs = freeVariables( nf )
      if ( !nf.isInstanceOf[FOLVar] ) {
        if ( !fvs.contains( y ) && !fvs.contains( z ) ) {
          rules += Rule( FOLFunction( A, x ), nf )
        }
        rules += Rule( FOLFunction( G, FOLFunction( "s", x ), y, z ), nf )

        if ( !fvs.contains( x ) )
          rules += Rule( FOLFunction( G, FOLFunction( "0" ), y, z ), nf )
      }

      rules += Rule( FOLFunction( G, FOLFunction( "s", x ), y, z ), FOLFunction( G, x, nf, z ) )
      if ( !fvs.contains( y ) && !fvs.contains( z ) ) {
        rules += Rule( FOLFunction( A, x ), FOLFunction( G, x, nf, x ) )
      }
    }

    RecursionScheme( rules.result() )
  }

}