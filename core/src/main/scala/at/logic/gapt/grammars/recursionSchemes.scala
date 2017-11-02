package at.logic.gapt.grammars

import at.logic.gapt.expr.fol._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature, MapBabelSignature }
import at.logic.gapt.provers.maxsat.{ MaxSATSolver, QMaxSAT, bestAvailableMaxSatSolver }
import at.logic.gapt.utils.{ Doc, Logger, metrics }

import scala.collection.mutable

case class Rule( lhs: Expr, rhs: Expr ) {
  require( freeVariables( rhs ) subsetOf freeVariables( lhs ), s"$rhs has more free variables than $lhs" )
  require( lhs.ty == rhs.ty, s"$lhs has different type than $rhs" )

  def apply( term: Expr ): Option[Expr] =
    syntacticMatching( lhs, term ).map( _( rhs ) )

  def apply( subst: Substitution ): Rule =
    Rule( subst( lhs ), subst( rhs ) )

  override def toString: String = toSigRelativeString
  def toSigRelativeString( implicit sig: BabelSignature ) = s"${lhs.toSigRelativeString} -> ${rhs.toSigRelativeString}"
}

private class RecursionSchemeExporter( unicode: Boolean, rs: RecursionScheme )
  extends BabelExporter( unicode, rs.babelSignature ) {

  import Doc._

  def csep( docs: List[Doc] ): Doc = wordwrap( docs, "," )

  def export(): String = {
    val nonTerminals = rs.startSymbol +: ( rs.nonTerminals - rs.startSymbol ).toList.sortBy { _.name }
    val ntDecl = group( "Non-terminals:" <> nest( line <> csep(
      nonTerminals map { show( _, false, Set(), Map(), prio.max )._1 } ) ) )

    val tDecl = group( "Terminals:" <> nest( line <> csep(
      rs.terminals.toList.sortBy { _.name } map { show( _, false, Set(), Map(), prio.max )._1 } ) ) )

    val knownTypes = ( rs.nonTerminals union rs.terminals ).map { c => c.name -> c }.toMap

    val rules = group( stack( rs.rules.toList sortBy { _.toString } map {
      case Rule( lhs, rhs ) =>
        group( show( lhs, false, Set(), knownTypes, prio.impl )._1 </> nest( "→" </>
          show( rhs, true, Set(), knownTypes, prio.impl )._1 ) )
    } ) )

    group( ntDecl </> tDecl <> line </> rules <> line ).render( lineWidth )
  }

}

case class RecursionScheme( startSymbol: Const, nonTerminals: Set[Const], rules: Set[Rule] ) {
  require( nonTerminals contains startSymbol )
  rules foreach {
    case Rule( Apps( leftHead: Const, _ ), _ ) =>
      require( nonTerminals contains leftHead )
  }

  def terminals: Set[Const] =
    rules flatMap { case Rule( lhs, rhs ) => constants( lhs ) union constants( rhs ) } diff nonTerminals

  def babelSignature = MapBabelSignature( terminals union nonTerminals )

  def language: Set[Expr] = parametricLanguage()
  def languageWithDummyParameters: Set[Expr] =
    startSymbol.ty match {
      case FunctionType( _, argtypes ) =>
        parametricLanguage( argtypes.zipWithIndex.map { case ( t, i ) => Const( s"dummy$i", t ) }: _* )
    }

  def rulesFrom( nonTerminal: Const ): Set[Rule] =
    rules collect { case r @ Rule( Apps( `nonTerminal`, _ ), _ ) => r }

  def parametricLanguage( params: Expr* ): Set[Expr] = {
    require( params.size == arity( startSymbol ) )
    generatedTerms( startSymbol( params: _* ) )
  }

  def generatedTerms( from: Expr ): Set[Expr] = {
    val seen = mutable.Set[Expr]()
    val gen = mutable.Set[Expr]()

    def rewrite( t: Expr ): Unit = t match {
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

  override def toString: String = new RecursionSchemeExporter( unicode = true, rs = this ).export()
}

object RecursionScheme {
  def apply( startSymbol: Const, rules: ( Expr, Expr )* ): RecursionScheme =
    apply( startSymbol, rules map { case ( from, to ) => Rule( from, to ) } toSet )

  def apply( startSymbol: Const, nonTerminals: Set[Const], rules: ( Expr, Expr )* ): RecursionScheme =
    RecursionScheme( startSymbol, nonTerminals, rules map { case ( from, to ) => Rule( from, to ) } toSet )

  def apply( startSymbol: Const, rules: Set[Rule] ): RecursionScheme = {
    val nonTerminals = rules.map { case Rule( Apps( head: Const, _ ), _ ) => head } + startSymbol
    RecursionScheme( startSymbol, nonTerminals, rules )
  }
}

object preOrderTraversal {
  def apply( term: Expr ): Seq[Expr] = term match {
    case App( a, b )       => term +: ( apply( a ) ++ apply( b ) )
    case _: Const | _: Var => Seq( term )
  }
}

object canonicalVars {
  def apply( term: Expr ): Expr =
    FOLSubstitution( preOrderTraversal( term ).
      collect { case v: FOLVar => v }.
      distinct.
      zipWithIndex.map { case ( v, i ) => v -> FOLVar( s"x$i" ) } )( term )
}

object TargetFilter {
  type Type = ( Expr, Expr ) => Option[Boolean]

  def default: Type = ( from: Expr, to: Expr ) =>
    syntacticMatching( to, from ) map { _ => true }
}

class RecSchemGenLangFormula(
    val recursionScheme: RecursionScheme,
    val targetFilter:    TargetFilter.Type = TargetFilter.default ) {

  def ruleIncluded( rule: Rule ) = FOLAtom( s"${rule.lhs}->${rule.rhs}" )
  def derivable( from: Expr, to: Expr ) = FOLAtom( s"$from=>$to" )

  private val rulesPerNonTerminal = Map() ++ recursionScheme.rules.
    groupBy { case Rule( _, Apps( nt: Const, _ ) ) => nt }.mapValues( _.toSeq )
  def reverseMatches( against: Expr ) =
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

  type Target = ( Expr, Expr )
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
          } ) )
    } ) ++ ( for (
      ( from1, to1 ) <- reachable;
      ( from2, to2 ) <- reachable if from1 == from2 && to1 != to2 if syntacticMatching( to2, to1 ).isDefined
    ) yield Imp( derivable( from1, to1 ), derivable( from1, to2 ) ) ) )
  }
}

object minimizeRecursionScheme extends Logger {
  def apply( recSchem: RecursionScheme, targets: Traversable[( Expr, Expr )],
             targetFilter: TargetFilter.Type = TargetFilter.default,
             solver:       MaxSATSolver      = bestAvailableMaxSatSolver,
             weight:       Rule => Int       = _ => 1 ) = {
    val fvs = freeVariables( targets.map( _._1 ) ) union freeVariables( targets.map( _._2 ) )
    val nameGen = rename.awayFrom( constants( targets.map( _._1 ) ) union constants( targets.map( _._2 ) ) )
    val grounding = Substitution( for ( v @ Var( name, ty ) <- fvs ) yield v -> Const( nameGen fresh name, ty ) )
    val targets_ = grounding( targets.toSet )

    val formula = new RecSchemGenLangFormula( recSchem, targetFilter )
    val hard = formula( targets_ )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> weight( rule ) }
    val interp = metrics.time( "maxsat" ) { solver.solve( hard, soft ).get }
    RecursionScheme( recSchem.startSymbol, recSchem.nonTerminals, recSchem.rules.filter { rule => interp( formula ruleIncluded rule ) } )
  }

  def viaInst( recSchem: RecursionScheme, targets: Traversable[( Expr, Expr )],
               targetFilter: TargetFilter.Type = TargetFilter.default,
               solver:       MaxSATSolver      = bestAvailableMaxSatSolver,
               weight:       Rule => Int       = _ => 1 ) = {
    val fvs = freeVariables( targets.map( _._1 ) ) union freeVariables( targets.map( _._2 ) )
    val nameGen = rename.awayFrom( constants( targets.map( _._1 ) ) union constants( targets.map( _._2 ) ) )
    val grounding = Substitution( for ( v @ Var( name, ty ) <- fvs ) yield v -> Const( nameGen fresh name, ty ) )
    val targets_ = grounding( targets.toSet )

    val instTerms = targets_.map { _._1 }.flatMap { case Apps( _, as ) => as }.flatMap { folSubTerms( _ ) }
    val instRS = instantiateRS( recSchem, instTerms )

    val formula = new RecSchemGenLangFormula( instRS, targetFilter )
    val ruleCorrespondence = for ( ir <- instRS.rules.toSeq ) yield formula.ruleIncluded( ir ) --> Or(
      for {
        r <- recSchem.rules.toSeq
        _ <- syntacticMatching( List( r.lhs -> ir.lhs, r.rhs -> ir.rhs ) )
      } yield formula.ruleIncluded( r ) )
    val hard = formula( targets_ ) & And( ruleCorrespondence )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> weight( rule ) }
    val interp = solver.solve( hard, soft ).get
    RecursionScheme( recSchem.startSymbol, recSchem.nonTerminals, recSchem.rules.filter { rule => interp( formula ruleIncluded rule ) } )
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
    FOLFunction( "G", FOLFunction( "s", FOLVar( "x" ) ), FOLVar( "y" ), FOLVar( "z" ) ) -> FOLVar( "t5" ) ) ) {

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

  def toTargets( instanceLanguages: Seq[stableSipGrammar.InstanceLanguage] ): Seq[( Expr, Expr )] =
    instanceLanguages flatMap {
      case ( n, l ) =>
        l map ( FOLFunction( A, Numeral( n ) ) -> _ )
    }

  def stableRecSchem( instanceLanguages: Seq[stableSipGrammar.InstanceLanguage] ): RecursionScheme =
    stableRecSchem( toTargets( instanceLanguages ) toSet )
}

case class RecSchemTemplate( startSymbol: Const, template: Set[( Expr, Expr )] ) {
  val nonTerminals: Set[Const] = template map { case ( Apps( nt: Const, _ ), _ ) => nt }

  val isSubtermC = "is_subterm"
  def isSubterm( v: Expr, t: Expr ): Formula =
    Const( isSubtermC, v.ty ->: t.ty ->: To )( v, t ).asInstanceOf[Formula]

  val canonicalArgs = nonTerminals map { case nt @ Const( _, FunctionType( _, argTypes ) ) => nt -> argTypes.zipWithIndex.map { case ( t, i ) => Var( s"${nt}_$i", t ) } } toMap
  val states = canonicalArgs map { case ( nt, args ) => nt( args: _* ) }
  val constraints: Map[( Const, Const ), Formula] = {
    val cache = mutable.Map[( Const, Const ), Formula]()

    def get( from: Const, to: Const ): Formula =
      cache.getOrElseUpdate( from -> to, {
        var postCond = if ( from == to )
          And( ( canonicalArgs( from ), canonicalArgs( to ) ).zipped map { Eq( _, _ ) } ) else Or( template collect {
          case ( Apps( prev: Const, prevArgs ), Apps( `to`, toArgs ) ) if prev != to =>
            def postCondition( preCond: Formula ): Formula = preCond match {
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

          def appRecConstr( p: Formula ): Formula = p match {
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

  val constraintEvaluators: Map[( Const, Const ), ( Seq[Expr], Seq[Expr] ) => Boolean] =
    constraints map {
      case ( ( from, to ), constr ) =>
        def mkEval( f: Formula ): ( ( Seq[Expr], Seq[Expr] ) => Boolean ) = f match {
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

  def stableRecSchem( targets: Set[( Expr, Expr )] ): RecursionScheme = {
    val neededVars = template flatMap { case ( from, to ) => freeVariables( from ) }

    val allTerms = targets map { _._2 }
    val topLevelStableTerms = stableTerms( allTerms, neededVars.toSeq ).filter( !_.isInstanceOf[Var] )
    val argumentStableTerms = stableTerms( allTerms flatMap { case Apps( _, as ) => as } flatMap { subTerms( _ ) } filter { _.ty.isInstanceOf[TBase] }, neededVars.toSeq )

    var rules = template.flatMap {
      case ( from, to: Var ) =>
        val allowedVars = freeVariables( from )
        topLevelStableTerms.filter { st => freeVariables( st ) subsetOf allowedVars }.
          map { Rule( from, _ ) }
      case ( from, to ) =>
        val allowedVars = freeVariables( from )
        val templateVars = freeVariables( to ).diff( freeVariables( from ) )
        templateVars.
          foldLeft( Seq[Map[Var, Expr]]( Map() ) )( ( chosenValues, nextVar ) =>
            for (
              subst <- chosenValues;
              st <- argumentStableTerms if st.ty == nextVar.ty && freeVariables( st ).subsetOf( allowedVars )
            ) yield subst + ( nextVar -> st ) ).
          map( s => Rule( from, Substitution( s )( to ) ) )
    }

    // Filter out rules that only used variables that are passed unchanged from the startSymbol.
    targets.map { case ( Apps( nt: Const, _ ), _ ) => nt }.toSeq match {
      case Seq() => // empty language
      case Seq( startSymbol ) =>
        ( nonTerminals - startSymbol ) foreach { nt =>
          constraints( startSymbol -> nt ) match {
            case And.nAry( constr ) =>
              val identicalArgs = constr.collect {
                case Eq( ntArg, startSymbolArg ) => canonicalArgs( nt ).indexOf( ntArg )
              }.toSet
              rules = rules filter {
                case Rule( Apps( `nt`, args ), to ) =>
                  !freeVariables( to ).subsetOf( identicalArgs map { args( _ ) } collect { case v: Var => v } )
                case _ => true
              }
          }
        }
    }

    RecursionScheme( startSymbol, nonTerminals, rules )
  }

  def findMinimalCover(
    targets: Set[( Expr, Expr )],
    solver:  MaxSATSolver        = bestAvailableMaxSatSolver,
    weight:  Rule => Int         = _ => 1 ): RecursionScheme = {
    minimizeRecursionScheme( stableRecSchem( targets ), targets toSeq, targetFilter, solver, weight )
  }
  def findMinimalCoverViaInst(
    targets: Set[( Expr, Expr )],
    solver:  MaxSATSolver        = bestAvailableMaxSatSolver,
    weight:  Rule => Int         = _ => 1 ): RecursionScheme = {
    minimizeRecursionScheme.viaInst( stableRecSchem( targets ), targets toSeq, targetFilter, solver, weight )
  }
}

object RecSchemTemplate {
  def apply( startSymbol: Const, rules: ( Expr, Expr )* ): RecSchemTemplate =
    RecSchemTemplate( startSymbol, rules toSet )
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

  def apply( recSchem: RecursionScheme ): VTRATG = {
    val nameGen = rename.awayFrom( containedNames( recSchem ) )

    val ntCorrespondence = orderedNonTerminals( recSchem ).reverse map {
      case nt @ Const( name, FunctionType( _, argTypes ) ) =>
        nt -> ( for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( nameGen.fresh( s"x_${name}_$i" ), t ) )
    }
    val ntMap = ntCorrespondence.toMap

    val FunctionType( startSymbolType, _ ) = recSchem.startSymbol.ty
    val startSymbol = Var( nameGen.fresh( s"x_${recSchem.startSymbol.name}" ), startSymbolType )
    val nonTerminals = List( startSymbol ) +: ( ntCorrespondence map { _._2 } filter { _.nonEmpty } )
    val productions = recSchem.rules map {
      case Rule( Apps( nt1: Const, vars1 ), Apps( nt2: Const, args2 ) ) if recSchem.nonTerminals.contains( nt1 ) && recSchem.nonTerminals.contains( nt2 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        ntMap( nt2 ) -> args2.map( subst( _ ) )
      case Rule( Apps( nt1: Const, vars1 ), rhs ) if recSchem.nonTerminals.contains( nt1 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        List( startSymbol ) -> List( subst( rhs ) )
    }
    VTRATG( startSymbol, nonTerminals, productions )
  }
}
