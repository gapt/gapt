package at.logic.gapt.grammars

import at.logic.gapt.expr.fol._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.provers.maxsat.{ bestAvailableMaxSatSolver, QMaxSAT, MaxSATSolver }
import at.logic.gapt.utils.logging.Logger

import scala.collection.mutable

case class Rule( lhs: LambdaExpression, rhs: LambdaExpression ) {
  require( freeVariables( rhs ) subsetOf freeVariables( lhs ), s"$rhs has more free variables than $lhs" )
  require( lhs.exptype == rhs.exptype, s"$lhs has different type than $rhs" )

  def apply( term: LambdaExpression ): Option[LambdaExpression] =
    syntacticMatching( lhs, term ).map( _( rhs ) )

  def apply( subst: Substitution ): Rule =
    Rule( subst( lhs ), subst( rhs ) )

  override def toString: String =
    s"$lhs -> $rhs"
}

case class RecursionScheme( axiom: Const, nonTerminals: Set[Const], rules: Set[Rule] ) {
  require( nonTerminals contains axiom )
  rules foreach {
    case Rule( Apps( leftHead: Const, _ ), _ ) =>
      require( nonTerminals contains leftHead )
  }

  def language: Set[LambdaExpression] = parametricLanguage()
  def languageWithDummyParameters: Set[LambdaExpression] =
    axiom.exptype match {
      case FunctionType( _, argtypes ) =>
        parametricLanguage( argtypes.zipWithIndex.map { case ( t, i ) => Const( s"dummy$i", t ) }: _* )
    }

  def rulesFrom( nonTerminal: Const ): Set[Rule] =
    rules collect { case r @ Rule( Apps( `nonTerminal`, _ ), _ ) => r }

  def parametricLanguage( params: LambdaExpression* ): Set[LambdaExpression] = {
    require( params.size == arity( axiom ) )
    generatedTerms( axiom( params: _* ) )
  }

  def generatedTerms( from: LambdaExpression ): Set[LambdaExpression] = {
    val seen = mutable.Set[LambdaExpression]()
    val gen = mutable.Set[LambdaExpression]()

    def rewrite( t: LambdaExpression ): Unit = t match {
      case _ if seen contains t => ()
      case Apps( head: Const, args ) if nonTerminals contains head =>
        rules foreach { _( t ) foreach rewrite }
        seen += t
      case _ =>
        gen += t
    }

    rewrite( from )
    gen.toSet
  }

  override def toString: String = rules.toSeq.sortBy( _.toString ) mkString "\n"
}

object RecursionScheme {
  def apply( axiom: Const, rules: ( LambdaExpression, LambdaExpression )* ): RecursionScheme =
    apply( axiom, rules map { case ( from, to ) => Rule( from, to ) } toSet )

  def apply( axiom: Const, nonTerminals: Set[Const], rules: ( LambdaExpression, LambdaExpression )* ): RecursionScheme =
    RecursionScheme( axiom, nonTerminals, rules map { case ( from, to ) => Rule( from, to ) } toSet )

  def apply( axiom: Const, rules: Set[Rule] ): RecursionScheme = {
    val nonTerminals = rules.map { case Rule( Apps( head: Const, _ ), _ ) => head } + axiom
    RecursionScheme( axiom, nonTerminals, rules )
  }
}

object preOrderTraversal {
  def apply( term: LambdaExpression ): Seq[LambdaExpression] = term match {
    case App( a, b )       => term +: ( apply( a ) ++ apply( b ) )
    case _: Const | _: Var => Seq( term )
  }
}

object canonicalVars {
  def apply( term: LambdaExpression ): LambdaExpression =
    FOLSubstitution( preOrderTraversal( term ).
      collect { case v: FOLVar => v }.
      distinct.
      zipWithIndex.map { case ( v, i ) => v -> FOLVar( s"x$i" ) } )( term )
}

object TargetFilter {
  type Type = ( LambdaExpression, LambdaExpression ) => Option[Boolean]

  def default: Type = ( from: LambdaExpression, to: LambdaExpression ) =>
    syntacticMatching( to, from ) map { _ => true }
}

class RecSchemGenLangFormula(
    val recursionScheme: RecursionScheme,
    val targetFilter:    TargetFilter.Type = TargetFilter.default
) {

  def ruleIncluded( rule: Rule ) = FOLAtom( s"${rule.lhs}->${rule.rhs}" )
  def derivable( from: LambdaExpression, to: LambdaExpression ) = FOLAtom( s"$from=>$to" )

  private val rulesPerNonTerminal = recursionScheme.rules.
    groupBy { case Rule( _, Apps( nt: Const, _ ) ) => nt }.mapValues( _.toSeq )
  def reverseMatches( against: LambdaExpression ) =
    against match {
      case Apps( nt: Const, _ ) => rulesPerNonTerminal.getOrElse( nt, Seq() ).flatMap { rule =>
        val ( fvsRule, fvsAgainst ) = ( freeVariables( rule.lhs ), freeVariables( against ) )
        val rule_ = if ( fvsRule intersect fvsAgainst nonEmpty )
          rule( Substitution( rename( freeVariables( rule.lhs ), freeVariables( against ) ) ) )
        else
          rule
        syntacticMGU( rule_.rhs, against ).headOption.map { unifier => canonicalVars( unifier( rule_.lhs ) ) -> rule }
      }
    }

  type Target = ( LambdaExpression, LambdaExpression )
  def apply( targets: Traversable[Target] ): FOLFormula = {
    val edges = mutable.ArrayBuffer[( Target, Rule, Target )]()
    val goals = mutable.Set[Target]()

    val queue = mutable.Queue( targets.toSeq: _* )
    val alreadyDone = mutable.Set[Target]()
    while ( queue nonEmpty ) {
      val target @ ( from, to ) = queue.dequeue()

      if ( !alreadyDone( target ) )
        reverseMatches( to ).foreach {
          case ( newTo, rule ) =>
            targetFilter( from, newTo ) match {
              case Some( true ) =>
                goals += ( from -> newTo )
                edges += ( ( target, rule, from -> newTo ) )
              case Some( false ) => ()
              case None =>
                edges += ( ( target, rule, from -> newTo ) )
                queue enqueue ( from -> newTo )
            }
        }

      alreadyDone += target
    }

    val reachable = mutable.Set[Target]( goals.toSeq: _* )
    var changed = true
    while ( changed ) {
      changed = false
      edges.foreach {
        case ( a, r, b ) =>
          if ( ( reachable contains b ) && !( reachable contains a ) ) {
            reachable += a
            changed = true
          }
      }
    }

    if ( !( targets.toSet subsetOf reachable ) ) return Bottom()

    val edgesPerFrom = edges.groupBy( _._1 )
    And( targets.toSeq.map { case ( from, to ) => derivable( from, to ) } ++ ( reachable collect {
      case t @ ( from, to ) if !( goals contains t ) =>
        Imp( derivable( from, to ), Or(
          edgesPerFrom( t ) collect {
            case ( _, r, b ) if goals contains b                      => ruleIncluded( r )
            case ( _, r, b @ ( from_, to_ ) ) if reachable contains b => And( ruleIncluded( r ), derivable( from_, to_ ) )
          }
        ) )
    } ) ++ ( for (
      ( from1, to1 ) <- reachable;
      ( from2, to2 ) <- reachable if from1 == from2 && to1 != to2 if syntacticMatching( to2, to1 ).isDefined
    ) yield Imp( derivable( from1, to1 ), derivable( from1, to2 ) ) ) )
  }
}

object minimizeRecursionScheme extends Logger {
  def apply( recSchem: RecursionScheme, targets: Traversable[( LambdaExpression, LambdaExpression )],
             targetFilter: TargetFilter.Type = TargetFilter.default,
             solver:       MaxSATSolver      = bestAvailableMaxSatSolver,
             weight:       Rule => Int       = _ => 1 ) = {
    val formula = new RecSchemGenLangFormula( recSchem, targetFilter )
    val hard = formula( targets )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> weight( rule ) }
    val interp = solver.solve( hard, soft ).get
    RecursionScheme( recSchem.axiom, recSchem.nonTerminals, recSchem.rules filter { rule => interp.interpret( formula ruleIncluded rule ) } )
  }
}

object SipRecSchem extends RecSchemTemplate(
  FOLFunctionConst( "A", 1 ),
  Set(
    FOLFunction( "A", FOLVar( "x" ) ) -> FOLVar( "t1" ),
    FOLFunction( "A", FOLVar( "x" ) ) ->
      FOLFunction( "G", FOLVar( "x" ), FOLVar( "x" ), FOLVar( "t2" ) ),
    FOLFunction( "G", FOLFunction( "s", FOLVar( "x" ) ), FOLVar( "y" ), FOLVar( "z" ) ) ->
      FOLFunction( "G", FOLVar( "x" ), FOLVar( "y" ), FOLVar( "t3" ) ),
    FOLFunction( "G", FOLFunction( "0" ), FOLVar( "y" ), FOLVar( "z" ) ) -> FOLVar( "t4" ),
    FOLFunction( "G", FOLFunction( "s", FOLVar( "x" ) ), FOLVar( "y" ), FOLVar( "z" ) ) -> FOLVar( "t5" )
  )
) {

  val A = "A"
  val G = "G"

  def toSipGrammar( recSchem: RecursionScheme ) =
    SipGrammar( recSchem.rules map {
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
    } map { p => p._1 -> p._2.asInstanceOf[FOLTerm] } )

  def toTargets( instanceLanguages: Seq[stableSipGrammar.InstanceLanguage] ): Seq[( LambdaExpression, LambdaExpression )] =
    instanceLanguages flatMap {
      case ( n, l ) =>
        l map ( FOLFunction( A, Numeral( n ) ) -> _ )
    }

  def stableRecSchem( instanceLanguages: Seq[stableSipGrammar.InstanceLanguage] ): RecursionScheme =
    stableRecSchem( toTargets( instanceLanguages ) toSet )
}

case class RecSchemTemplate( axiom: Const, template: Set[( LambdaExpression, LambdaExpression )] ) {
  val nonTerminals: Set[Const] = template map { case ( Apps( nt: Const, _ ), _ ) => nt }

  val isSubtermC = "is_subterm"
  def isSubterm( v: LambdaExpression, t: LambdaExpression ): HOLFormula =
    Const( isSubtermC, v.exptype -> ( t.exptype -> To ) )( v, t ).asInstanceOf[HOLFormula]

  val canonicalArgs = nonTerminals map { case nt @ Const( _, FunctionType( _, argTypes ) ) => nt -> argTypes.zipWithIndex.map { case ( t, i ) => Var( s"${nt}_$i", t ) } } toMap
  val states = canonicalArgs map { case ( nt, args ) => nt( args: _* ) }
  val constraints: Map[( Const, Const ), HOLFormula] = {
    val cache = mutable.Map[( Const, Const ), HOLFormula]()

    def get( from: Const, to: Const ): HOLFormula =
      cache.getOrElseUpdate( from -> to, {
        var postCond = if ( from == to )
          And( ( canonicalArgs( from ), canonicalArgs( to ) ).zipped map { Eq( _, _ ) } ) else Or( template collect {
          case ( Apps( prev: Const, prevArgs ), Apps( `to`, toArgs ) ) if prev != to =>
            def postCondition( preCond: HOLFormula ): HOLFormula = preCond match {
              case Top()       => Top()
              case Bottom()    => Bottom()
              case And( a, b ) => And( postCondition( a ), postCondition( b ) )
              case Or( a, b )  => Or( postCondition( a ), postCondition( b ) )

              case Eq( a, b ) =>
                prevArgs( canonicalArgs( prev ).indexOf( a ) ) match {
                  case v: Var =>
                    And( for ( ( toArg, canToArg: Var ) <- ( toArgs, canonicalArgs( to ) ).zipped.toSeq if v == toArg )
                      yield Eq( canToArg, b ) )
                  case constr =>
                    val vars = freeVariables( constr )
                    And( ( toArgs.toSeq zip canonicalArgs( to ) ).
                      collect {
                        case ( toArg: Var, canToArg ) if vars contains toArg =>
                          isSubterm( canToArg, b )
                      } )
                }

              case Apps( Const( `isSubtermC`, _ ), Seq( a, b ) ) =>
                val vars = freeVariables( prevArgs( canonicalArgs( prev ).indexOf( a ) ) )
                And( ( toArgs.toSeq zip canonicalArgs( to ) ).
                  collect {
                    case ( toArg: Var, canToArg ) if vars contains toArg =>
                      isSubterm( canToArg, b )
                  } )
            }
            postCondition( get( from, prev ) )
        } toSeq )

        val recCalls = template filter {
          case ( Apps( `to`, _ ), Apps( `to`, _ ) ) => true
          case _                                    => false
        }
        if ( recCalls nonEmpty ) {
          val constArgs = canonicalArgs( to ).zipWithIndex filter {
            case ( a, i ) =>
              recCalls forall {
                case ( Apps( _, callerArgs ), Apps( _, calleeArgs ) ) =>
                  callerArgs( i ) == calleeArgs( i )
              }
          } map { _._1 }

          val structRecArgs = canonicalArgs( to ).zipWithIndex filter {
            case ( a, i ) =>
              recCalls forall {
                case ( Apps( _, callerArgs ), Apps( _, calleeArgs ) ) =>
                  callerArgs( i ).find( calleeArgs( i ) ).nonEmpty
              }
          } map { _._1 }

          def appRecConstr( p: HOLFormula ): HOLFormula = p match {
            case Top()                                  => Top()
            case Bottom()                               => Bottom()
            case Or( a, b )                             => Or( appRecConstr( a ), appRecConstr( b ) )
            case And( a, b )                            => And( appRecConstr( a ), appRecConstr( b ) )
            case Eq( a, b ) if constArgs contains a     => Eq( a, b )
            case Eq( a, b ) if structRecArgs contains a => isSubterm( a, b )
            case Apps( Const( `isSubtermC`, _ ), Seq( a, b ) ) if ( constArgs contains a ) || ( structRecArgs contains a ) =>
              isSubterm( a, b )
            case _ => Top()
          }

          postCond = appRecConstr( postCond )
        }

        simplify( toNNF( postCond ) )
      } )

    ( for ( from <- nonTerminals; to <- nonTerminals )
      yield ( from, to ) -> get( from, to ) ) toMap
  }

  val constraintEvaluators: Map[( Const, Const ), ( Seq[LambdaExpression], Seq[LambdaExpression] ) => Boolean] =
    constraints map {
      case ( ( from, to ), constr ) =>
        def mkEval( f: HOLFormula ): ( ( Seq[LambdaExpression], Seq[LambdaExpression] ) => Boolean ) = f match {
          case Top() => ( _, _ ) => true
          case Bottom() => ( _, _ ) => false
          case And( a, b ) =>
            val aEval = mkEval( a )
            val bEval = mkEval( b )
            ( x, y ) => aEval( x, y ) && bEval( x, y )
          case Or( a, b ) =>
            val aEval = mkEval( a )
            val bEval = mkEval( b )
            ( x, y ) => aEval( x, y ) || bEval( x, y )
          case Eq( b, a ) =>
            val aIdx = canonicalArgs( from ).indexOf( a )
            val bIdx = canonicalArgs( to ).indexOf( b )
            require( aIdx >= 0 && bIdx >= 0 )
            ( x, y ) => syntacticMatching( y( bIdx ), x( aIdx ) ).isDefined
          case Apps( Const( `isSubtermC`, _ ), Seq( b, a ) ) =>
            val aIdx = canonicalArgs( from ).indexOf( a )
            val bIdx = canonicalArgs( to ).indexOf( b )
            require( aIdx >= 0 && bIdx >= 0 )
            ( x, y ) => ( expressionSize( y( bIdx ) ) <= expressionSize( x( aIdx ) ) + 1 ) &&
              constants( y( bIdx ) ).subsetOf( constants( x( aIdx ) ) )
        }
        ( from -> to ) -> mkEval( constr )
    }

  val targetFilter: TargetFilter.Type = ( from, to ) =>
    TargetFilter.default( from, to ).orElse {
      val Apps( fromNt: Const, fromArgs ) = from
      val Apps( toNt: Const, toArgs ) = to
      val constrValue = constraintEvaluators( fromNt -> toNt )( fromArgs, toArgs )
      if ( constrValue ) None else Some( false )
    }

  def stableRecSchem( targets: Set[( LambdaExpression, LambdaExpression )] ): RecursionScheme = {
    val neededVars = template flatMap { case ( from, to ) => freeVariables( from ) }

    val allTerms = targets map { _._2 }
    val topLevelStableTerms = stableTerms( allTerms, neededVars.toSeq ).filter( !_.isInstanceOf[Var] )
    val argumentStableTerms = stableTerms( allTerms flatMap { case Apps( _, as ) => as } flatMap { subTerms( _ ) } filter { _.exptype.isInstanceOf[TBase] }, neededVars.toSeq )

    var rules = template.flatMap {
      case ( from, to: Var ) =>
        val allowedVars = freeVariables( from )
        topLevelStableTerms.filter { st => freeVariables( st ) subsetOf allowedVars }.
          map { Rule( from, _ ) }
      case ( from, to ) =>
        val allowedVars = freeVariables( from )
        val templateVars = freeVariables( to ).diff( freeVariables( from ) )
        templateVars.
          foldLeft( Seq[Map[Var, LambdaExpression]]( Map() ) )( ( chosenValues, nextVar ) =>
            for (
              subst <- chosenValues;
              st <- argumentStableTerms if st.exptype == nextVar.exptype && freeVariables( st ).subsetOf( allowedVars )
            ) yield subst + ( nextVar -> st ) ).
          map( s => Rule( from, Substitution( s )( to ) ) )
    }

    // Filter out rules that only used variables that are passed unchanged from the axiom.
    targets.map { case ( Apps( nt: Const, _ ), _ ) => nt }.toSeq match {
      case Seq( axiom ) =>
        ( nonTerminals - axiom ) foreach { nt =>
          constraints( axiom -> nt ) match {
            case And.nAry( constr ) =>
              val identicalArgs = constr.collect {
                case Eq( ntArg, axiomArg ) => canonicalArgs( nt ).indexOf( ntArg )
              }.toSet
              rules = rules filter {
                case Rule( Apps( `nt`, args ), to ) =>
                  !freeVariables( to ).subsetOf( identicalArgs map { args( _ ).asInstanceOf[Var] } )
                case _ => true
              }
          }
        }
    }

    RecursionScheme( axiom, nonTerminals, rules )
  }

  def findMinimalCover( targets: Set[( LambdaExpression, LambdaExpression )], solver: MaxSATSolver = bestAvailableMaxSatSolver ): RecursionScheme = {
    minimizeRecursionScheme( stableRecSchem( targets ), targets toSeq, targetFilter, solver )
  }
}

object RecSchemTemplate {
  def apply( axiom: Const, rules: ( LambdaExpression, LambdaExpression )* ): RecSchemTemplate =
    RecSchemTemplate( axiom, rules toSet )
}

object recSchemToVTRATG {
  def orderedNonTerminals( rs: RecursionScheme ): Seq[Const] = {
    val ntDeps = rs.nonTerminals map { nt =>
      nt -> ( rs rulesFrom nt map { _.rhs } flatMap { constants( _ ) } intersect rs.nonTerminals )
    } toMap

    var nts = Seq[Const]()
    while ( rs.nonTerminals -- nts nonEmpty ) {
      val Some( next ) = rs.nonTerminals -- nts find { nt => ntDeps( nt ) subsetOf nts.toSet }
      nts = next +: nts
    }
    nts
  }

  def apply( recSchem: RecursionScheme ): VectTratGrammar = {
    val ntCorrespondence = orderedNonTerminals( recSchem ).reverse map {
      case nt @ Const( name, FOLHeadType( Ti, n ) ) =>
        nt -> ( 0 until n ).map { i => FOLVar( s"${name}_$i" ) }.toList
    }
    val ntMap = ntCorrespondence.toMap

    val axiom = FOLVar( "τ" )
    val nonTerminals = List( axiom ) +: ( ntCorrespondence map { _._2 } filter { _.nonEmpty } )
    val productions = recSchem.rules map {
      case Rule( Apps( nt1: Const, vars1 ), Apps( nt2: Const, args2 ) ) if recSchem.nonTerminals.contains( nt1 ) && recSchem.nonTerminals.contains( nt2 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        ntMap( nt2 ) -> args2.map( subst( _ ) ).map( _.asInstanceOf[FOLTerm] )
      case Rule( Apps( nt1: Const, vars1 ), rhs ) if recSchem.nonTerminals.contains( nt1 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        List( axiom ) -> List( subst( rhs ).asInstanceOf[FOLTerm] )
    }
    VectTratGrammar( axiom, nonTerminals, productions )
  }
}

object qbupForRecSchem {
  def apply( recSchem: RecursionScheme ): HOLFormula = {
    def convert( term: LambdaExpression ): HOLFormula = term match {
      case Apps( ax, _ ) if ax == recSchem.axiom => Bottom()
      case Apps( nt @ Const( name, ty ), args ) if recSchem.nonTerminals contains nt =>
        HOLAtom( Var( s"X_$name", ty )( args: _* ) )
      case formula => -formula
    }

    existsclosure( And( recSchem.rules groupBy { _.lhs } map {
      case ( lhs, rules ) =>
        All.Block(
          freeVariables( lhs ) toSeq,
          And( rules map { _.rhs } map convert toSeq ) --> convert( lhs )
        )
    } toSeq ) )
  }
}
