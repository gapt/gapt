package gapt.grammars

import gapt.expr.formula.fol._
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol._
import gapt.expr.subst.FOLSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.ty.arity
import gapt.expr.util.constants
import gapt.expr.util.expressionSize
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.expr.util.subTerms
import gapt.expr.util.syntacticMGU
import gapt.expr.util.syntacticMatching
import gapt.formats.babel.{ BabelExporter, BabelSignature, MapBabelSignature, Precedence }
import gapt.logic.hol.simplify
import gapt.logic.hol.toNNF
import gapt.proofs.context.Context
import gapt.provers.maxsat.{ MaxSATSolver, bestAvailableMaxSatSolver }
import gapt.utils.{ Doc, Logger }

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
      nonTerminals map { show( _, false, Map(), Map() )._1.inPrec( 0 ) } ) ) )

    val tDecl = group( "Terminals:" <> nest( line <> csep(
      rs.terminals.toList.sortBy { _.name } map { show( _, false, Map(), Map() )._1.inPrec( 0 ) } ) ) )

    val knownTypes = ( rs.nonTerminals union rs.terminals ).map { c => c.name -> c }.toMap

    val rules = group( stack( rs.rules.toList sortBy { _.toString } map {
      case Rule( lhs, rhs ) =>
        group( show( lhs, false, Map(), knownTypes )._1.inPrec( Precedence.impl ) </> nest( "→" </>
          show( rhs, true, Map(), knownTypes )._1.inPrec( Precedence.impl ) ) )
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
    groupBy { case Rule( _, Apps( nt: Const, _ ) ) => nt }.view.mapValues( _.toSeq ).toMap
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
  def apply( targets: Iterable[Target] ): FOLFormula = {
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
            case ( _, r, b ) if goals contains b => ruleIncluded( r )
            case ( _, r, b @ ( from_, to_ ) ) if reachable contains b =>
              And( ruleIncluded( r ), derivable( from_, to_ ) )
          } ) )
    } ) ++ ( for (
      ( from1, to1 ) <- reachable;
      ( from2, to2 ) <- reachable if from1 == from2 && to1 != to2 if syntacticMatching( to2, to1 ).isDefined
    ) yield Imp( derivable( from1, to1 ), derivable( from1, to2 ) ) ) )
  }
}

object minimizeRecursionScheme {
  val logger = Logger( "minimizeRecursionScheme" ); import logger._

  def apply( recSchem: RecursionScheme, targets: Iterable[( Expr, Expr )],
             targetFilter: TargetFilter.Type = TargetFilter.default,
             solver:       MaxSATSolver      = bestAvailableMaxSatSolver,
             weight:       Rule => Int = _ => 1 ) = {
    val fvs = freeVariables( targets.map( _._1 ) ) union freeVariables( targets.map( _._2 ) )
    val nameGen = rename.awayFrom( constants( targets.map( _._1 ) ) union constants( targets.map( _._2 ) ) )
    val grounding = Substitution( for ( v @ Var( name, ty ) <- fvs ) yield v -> Const( nameGen fresh name, ty ) )
    val targets_ = grounding( targets.toSet )

    val formula = new RecSchemGenLangFormula( recSchem, targetFilter )
    val hard = formula( targets_ )
    debug( s"Logical complexity of the minimization formula: ${lcomp( simplify( toNNF( hard ) ) )}" )
    val soft = recSchem.rules map { rule => Neg( formula.ruleIncluded( rule ) ) -> weight( rule ) }
    val interp = time( "maxsat" ) { solver.solve( hard, soft ).get }
    RecursionScheme( recSchem.startSymbol, recSchem.nonTerminals,
      recSchem.rules.filter { rule => interp( formula ruleIncluded rule ) } )
  }

  def viaInst( recSchem: RecursionScheme, targets: Iterable[( Expr, Expr )],
               targetFilter: TargetFilter.Type = TargetFilter.default,
               solver:       MaxSATSolver      = bestAvailableMaxSatSolver,
               weight:       Rule => Int = _ => 1 ) = {
    val fvs = freeVariables( targets.map( _._1 ) ) union freeVariables( targets.map( _._2 ) )
    val nameGen = rename.awayFrom( constants( targets.map( _._1 ) ) union constants( targets.map( _._2 ) ) )
    val grounding = Substitution( for ( v @ Var( name, ty ) <- fvs ) yield v -> Const( nameGen fresh name, ty ) )
    val targets_ = grounding( targets.toSet )

    val instTerms = targets_.map { _._1 }.flatMap { case Apps( _, as ) => as }.flatMap { flatSubterms( _ ) }
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
    RecursionScheme( recSchem.startSymbol, recSchem.nonTerminals,
      recSchem.rules.filter { rule => interp( formula ruleIncluded rule ) } )
  }
}

case class RecSchemTemplate( startSymbol: Const, template: Set[( Expr, Expr )] ) {
  val nonTerminals: Set[Const] = template map { case ( Apps( nt: Const, _ ), _ ) => nt }

  val isSubtermC = "is_subterm"
  def isSubterm( v: Expr, t: Expr ): Formula =
    Const( isSubtermC, v.ty ->: t.ty ->: To )( v, t ).asInstanceOf[Formula]

  val canonicalArgs = nonTerminals map {
    case nt @ Const( _, FunctionType( _, argTypes ), _ ) =>
      nt -> argTypes.zipWithIndex.map { case ( t, i ) => Var( s"${nt}_$i", t ) }
  } toMap
  val states = canonicalArgs map { case ( nt, args ) => nt( args: _* ) }
  val constraints: Map[( Const, Const ), Formula] = {
    val cache = mutable.Map[( Const, Const ), Formula]()

    def get( from: Const, to: Const ): Formula =
      cache.getOrElseUpdate( from -> to, {
        var postCond = if ( from == to )
          And( canonicalArgs( from ).lazyZip( canonicalArgs( to ) ).map { Eq( _, _ ) } ) else Or( template collect {
          case ( Apps( prev: Const, prevArgs ), Apps( `to`, toArgs ) ) if prev != to =>
            def postCondition( preCond: Formula ): Formula = preCond match {
              case Top()       => Top()
              case Bottom()    => Bottom()
              case And( a, b ) => And( postCondition( a ), postCondition( b ) )
              case Or( a, b )  => Or( postCondition( a ), postCondition( b ) )

              case Eq( a, b ) =>
                prevArgs( canonicalArgs( prev ).indexOf( a ) ) match {
                  case v: Var =>
                    And( for ( ( toArg, canToArg: Var ) <- toArgs.lazyZip( canonicalArgs( to ) ).toSeq if v == toArg )
                      yield Eq( canToArg, b ) )
                  case constr =>
                    val vars = freeVariables( constr )
                    And( ( toArgs.toSeq zip canonicalArgs( to ) ).
                      collect {
                        case ( toArg: Var, canToArg ) if vars contains toArg =>
                          isSubterm( canToArg, b )
                      } )
                }

              case Apps( Const( `isSubtermC`, _, _ ), Seq( a, b ) ) =>
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
            case Apps( Const( `isSubtermC`, _, _ ), Seq( a, b )
              ) if ( constArgs contains a ) || ( structRecArgs contains a ) =>
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
          case Apps( Const( `isSubtermC`, _, _ ), Seq( b, a ) ) =>
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
    val argumentStableTerms = stableTerms(
      allTerms
        flatMap { case Apps( _, as ) => as }
        flatMap { subTerms( _ ) }
        filter { _.ty.isInstanceOf[TBase] },
      neededVars.toSeq )

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
    weight:  Rule => Int = _ => 1 ): RecursionScheme = {
    minimizeRecursionScheme( stableRecSchem( targets ), targets toSeq, targetFilter, solver, weight )
  }
  def findMinimalCoverViaInst(
    targets: Set[( Expr, Expr )],
    solver:  MaxSATSolver        = bestAvailableMaxSatSolver,
    weight:  Rule => Int = _ => 1 ): RecursionScheme = {
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
      case nt @ Const( name, FunctionType( _, argTypes ), _ ) =>
        nt -> ( for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( nameGen.fresh( s"x_${name}_$i" ), t ) )
    }
    val ntMap = ntCorrespondence.toMap

    val FunctionType( startSymbolType, _ ) = recSchem.startSymbol.ty
    val startSymbol = Var( nameGen.fresh( s"x_${recSchem.startSymbol.name}" ), startSymbolType )
    val nonTerminals = List( startSymbol ) +: ( ntCorrespondence map { _._2 } filter { _.nonEmpty } )
    val productions = recSchem.rules map {
      case Rule( Apps( nt1: Const, vars1 ), Apps( nt2: Const, args2 )
        ) if recSchem.nonTerminals.contains( nt1 ) && recSchem.nonTerminals.contains( nt2 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        ntMap( nt2 ) -> args2.map( subst( _ ) )
      case Rule( Apps( nt1: Const, vars1 ), rhs ) if recSchem.nonTerminals.contains( nt1 ) =>
        val subst = Substitution( vars1.map( _.asInstanceOf[Var] ) zip ntMap( nt1 ) )
        List( startSymbol ) -> List( subst( rhs ) )
    }
    VTRATG( startSymbol, nonTerminals, productions )
  }
}

object simplePi1RecSchemTempl {
  def apply( startSymbol: Expr, pi1QTys: Seq[TBase] )( implicit ctx: Context ): RecSchemTemplate = {
    val nameGen = rename.awayFrom( ctx.constants )

    val Apps( startSymbolNT: Const, startSymbolArgs ) = startSymbol
    val FunctionType( instTT, startSymbolArgTys ) = startSymbolNT.ty
    // TODO: handle strong quantifiers in conclusion correctly
    val startSymbolArgs2 = for ( ( t, i ) <- startSymbolArgTys.zipWithIndex ) yield Var( s"x_$i", t )

    val indLemmaNT = Const(
      nameGen fresh "B",
      FunctionType( instTT, startSymbolArgTys ++ startSymbolArgTys ++ pi1QTys ) )

    val lhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w_$i", t )
    val rhsPi1QArgs = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"v_$i", t )

    val indLemmaRules = startSymbolArgTys.zipWithIndex.flatMap {
      case ( indLemmaArgTy, indLemmaArgIdx ) =>
        val indTy = indLemmaArgTy.asInstanceOf[TBase]
        ctx.getConstructors( indTy ) match {
          case None => Seq()
          case Some( ctrs ) =>
            ctrs flatMap { ctr =>
              val FunctionType( _, ctrArgTys ) = ctr.ty
              val ctrArgs = for ( ( t, i ) <- ctrArgTys.zipWithIndex )
                yield Var( s"x_${indLemmaArgIdx}_$i", t )
              val lhs = indLemmaNT( startSymbolArgs )(
                startSymbolArgs2.take( indLemmaArgIdx ) )(
                  ctr( ctrArgs: _* ) )(
                    startSymbolArgs2.drop( indLemmaArgIdx + 1 ) )(
                      lhsPi1QArgs )
              val recRules = ctrArgTys.zipWithIndex.filter { _._1 == indTy } map {
                case ( ctrArgTy, ctrArgIdx ) =>
                  lhs -> indLemmaNT( startSymbolArgs )(
                    startSymbolArgs2.take( indLemmaArgIdx ) )(
                      ctrArgs( ctrArgIdx ) )(
                        startSymbolArgs2.drop( indLemmaArgIdx + 1 ) )(
                          rhsPi1QArgs )
              }
              recRules :+ ( lhs -> Var( "u", instTT ) )
            }
        }
    }

    RecSchemTemplate(
      startSymbolNT,
      indLemmaRules.toSet
        + ( startSymbolNT( startSymbolArgs ) ->
          indLemmaNT( startSymbolArgs )( startSymbolArgs )( rhsPi1QArgs ) )
          + ( startSymbolNT( startSymbolArgs ) -> Var( "u", instTT ) )
          + ( indLemmaNT( startSymbolArgs )( startSymbolArgs2 )( lhsPi1QArgs ) -> Var( "u", instTT ) ) )
  }
}

object qbupForRecSchem {
  def canonicalRsLHS( recSchem: RecursionScheme )( implicit ctx: Context ): Set[Expr] =
    recSchem.nonTerminals flatMap { nt =>
      val FunctionType( To, argTypes ) = nt.ty
      val args = for ( ( t, i ) <- argTypes.zipWithIndex ) yield Var( s"x$i", t )
      recSchem.rulesFrom( nt ).flatMap {
        case Rule( Apps( _, as ), _ ) => as.zipWithIndex.filterNot { _._1.isInstanceOf[Var] }.map { _._2 }
      }.toSeq match {
        case Seq() => Some( nt( args: _* ) )
        case idcs =>
          val newArgs = for ( ( _: TBase, idx ) <- argTypes.zipWithIndex )
            yield if ( !idcs.contains( idx ) ) List( args( idx ) )
          else {
            val indTy = argTypes( idx ).asInstanceOf[TBase]
            val Some( ctrs ) = ctx.getConstructors( indTy )
            for {
              ctr <- ctrs.toList
              FunctionType( _, ctrArgTys ) = ctr.ty
            } yield ctr(
              ( for ( ( t, i ) <- ctrArgTys.zipWithIndex ) yield Var( s"x${idx}_$i", t ) ): _* )
          }
          import cats.instances.list._
          import cats.syntax.traverse._
          newArgs.traverse( identity ).map( nt( _: _* ) )
      }
    }

  def apply( recSchem: RecursionScheme, conj: Formula )( implicit ctx: Context ): Formula = {
    def convert( term: Expr ): Formula = term match {
      case Apps( ax, args ) if ax == recSchem.startSymbol => instantiate( conj, args )
      case Apps( nt @ Const( name, ty, _ ), args ) if recSchem.nonTerminals contains nt =>
        Atom( Var( s"X_$name", ty )( args: _* ) )
      case formula: Formula => formula
    }

    val lhss = canonicalRsLHS( recSchem )

    existentialClosure( And( for ( lhs <- lhss ) yield All.Block(
      freeVariables( lhs ) toSeq,
      formulaToSequent.pos( And( for {
        Rule( lhs_, rhs ) <- recSchem.rules
        subst <- syntacticMatching( lhs_, lhs )
      } yield convert( subst( rhs ) ) )
        --> convert( lhs ) ).toImplication ) ) )
  }
}
