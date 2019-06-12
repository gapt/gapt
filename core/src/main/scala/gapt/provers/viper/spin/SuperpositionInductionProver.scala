package gapt.provers.viper.spin

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.ty.{ TArr, TBase, Ty }
import gapt.expr.util.{ LambdaPosition, constants, variables }
import gapt.formats.tip.{ ConditionalNormalizer, ConditionalReductionRule, TipProblem }
import gapt.logic.hol.skolemize
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.lk.LKProof
import gapt.proofs.{ HOLSequent, Sequent, withSection }
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule
import gapt.proofs.resolution.{ ResolutionToLKProof, mapInputClauses, structuralCNF }
import gapt.provers.escargot.Escargot
import gapt.provers.escargot.impl.EscargotLogger
import gapt.provers.sat.Sat4j
import gapt.provers.viper.aip.axioms.{ Axiom, SequentialInductionAxioms, StandardInductionAxioms }
import gapt.provers.viper.grammars.enumerateTerms
import gapt.utils.NameGenerator

// TODO: sampleTestTerms should probably not be 5 but something dependent on the number of constructors
case class SpinOptions(
    performGeneralization: Boolean = true,
    sampleTestTerms:       Int     = 5 )

object SuperpositionInductionProver {
  def apply( problem: TipProblem ): SuperpositionInductionProver =
    new SuperpositionInductionProver( SpinOptions(), problem )

  def apply( opts: SpinOptions, problem: TipProblem ): SuperpositionInductionProver =
    new SuperpositionInductionProver( opts, problem )
}

class SuperpositionInductionProver( opts: SpinOptions, problem: TipProblem ) {
  val performGeneralization: Boolean = opts.performGeneralization

  private implicit def labeledSequentToHOLSequent( sequent: Sequent[( String, Formula )] ): Sequent[Formula] =
    sequent map { case ( _, f ) => f }

  val ctx: ImmutableContext = problem.ctx
  private val conditionalRefl = reflRules( ctx ).map( ConditionalReductionRule( _ ) )

  // Split on the refl rules as well to treat = as having two primary positions
  val allPositions: Map[Const, Positions] = Positions.splitRules( problem.reductionRules.toSet ++ conditionalRefl )
  val nameGen: NameGenerator = ctx.newNameGenerator
  val sat = new Sat4j()

  val normalizer: ConditionalNormalizer =
    ConditionalNormalizer(
      problem.reductionRules.toSet ++ conditionalRefl ++ simplificationRules.conditionalRules ++
        constructorRules( ctx ).map( ConditionalReductionRule( _ ) ) )

  // Ignore non-normalized counter examples if the problem has lambdas
  val acceptNotNormalized: Boolean = ctx.names.exists( lambdaType )

  // Is c an inductive skolem constant, i.e. not a constructor
  def isInductive( c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( c.ty ) match {
      case None => false
      case Some( constrs ) =>
        !constrs.contains( c ) && !problem.reductionRules.exists( rule => rule.lhsHead == c )
    }

  def asInductiveConst( e: Expr )( implicit ctx: Context ): Option[Const] =
    e match {
      case c @ Const( _, _, _ ) if isInductive( c ) => Some( c )
      case _                                        => None
    }

  def funHeaded( e: Expr ): Boolean =
    e match {
      case Apps( c @ Const( _, _, _ ), _ ) =>
        problem.reductionRules.exists( _.lhsHead == c ) && !lambdaType( c.ty.toString )
      case _ => false
    }

  /**
   * Proves the given sequent by using induction.
   *
   * @param sequent The sequent to be proven.
   * @param ctx Defines the constants, types, etc.
   * @return An inductive proof the sequent is provable with the prover's induction schemes, otherwise None or
   *         the method does not terminate.
   */
  def inductiveLKProof( sequent: Sequent[( String, Formula )] )( implicit ctx: MutableContext ): Option[LKProof] = {
    val seq = labeledSequentToHOLSequent( sequent )

    withSection { section =>
      val ground = section.groundSequent( seq )

      // Perform an initial induction while the goal has not been split across several clauses
      val goals = ground.succedent
      val goalAxioms = goals flatMap ( goal => clauseAxioms( skolemize( goal ) +: Sequent() )( ctx ) )
      val goalGround = goalAxioms.map( _.formula ) ++: ground

      val cnf = structuralCNF( goalGround )( ctx )
      val cnfMap = cnf.view.map( p => p.conclusion -> p ).toMap

      val clauses = cnfMap.keySet.map( _.map( _.asInstanceOf[Atom] ) )

      val prf = Escargot.getResolutionProofWithAxioms( clauses, Some( this ) )

      prf map {
        case ( resolution, prfAxioms, indMap ) =>
          val axioms = goalAxioms ++ prfAxioms.toSeq
          val res = mapInputClauses( resolution )( cnfMap ++ indMap )
          val lk = ResolutionToLKProof( res )
          val wlk = WeakeningContractionMacroRule( lk, axioms.map( _.formula ) ++: ground )
          val cut = cutAxioms( wlk, axioms )
          cut
      }
    }
  }

  /**
   * Cuts the specified axioms from the proof.
   *
   * @param proof The proof from which some axioms are to be cut. The end-sequent of this proof must
   *              contain the given axioms.
   * @param axioms The axioms to be cut out of the proof.
   * @return A proof whose end-sequent does not contain the specified axioms.
   */
  private def cutAxioms( proof: LKProof, axioms: Seq[Axiom] ): LKProof =
    axioms.foldRight( proof ) { ( axiom, mainProof ) =>
      if ( mainProof.conclusion.antecedent contains axiom.formula )
        CutRule( axiom.proof, mainProof, axiom.formula )
      else
        mainProof
    }

  // Equality is reflexive for all base types
  def reflRules( ctx: Context ): Set[ReductionRule] = {
    val baseTypes = ctx.get[BaseTypes].baseTypes.values.toSet

    baseTypes.map { ty =>
      val x = Var( "x", ty )
      ReductionRule( Eq( x, x ), Top() )
    }
  }

  // Reduction rules for reducing equalities between equal constructors to equalities on their arguments
  // and equalities between distinct constructors to bottom.
  def constructorRules( ctx: Context ): Set[ReductionRule] = {
    def makeArgs( ty: Ty ): List[Var] =
      ty match {
        case TArr( s, t ) => Var( nameGen.fresh( "arg" ), s ) :: makeArgs( t )
        case _            => List()
      }

    val baseTypes = ctx.get[BaseTypes].baseTypes.values
    val constructors = baseTypes.flatMap( ty => ctx.getConstructors( ty ).getOrElse( List() ) ).toSet

    val same = constructors.map { constr =>
      val lhsArgs = makeArgs( constr.ty )
      val rhsArgs = makeArgs( constr.ty )

      val res = lhsArgs.zip( rhsArgs )
        .foldLeft( Top().asInstanceOf[Formula] ) { case ( acc, ( l, r ) ) => And( acc, Eq( l, r ) ) }

      ReductionRule( Eq( Apps( constr, lhsArgs ), Apps( constr, rhsArgs ) ), res )
    }

    val diff = constructors.flatMap { constr1 =>
      constructors.filter( constr2 => constr1 != constr2 && resType( constr1.ty ) == resType( constr2.ty ) ).map { constr2 =>
        val lhsArgs = makeArgs( constr1.ty )
        val rhsArgs = makeArgs( constr2.ty )

        ReductionRule( Eq( Apps( constr1, lhsArgs ), Apps( constr2, rhsArgs ) ), Bottom() )
      }
    }

    same ++ diff
  }

  // Replace universals and existentials with a fixed number of tests of the formula
  def unfoldQuantifiers( e: Expr )( implicit ctx: Context ): Expr = {
    def samples( x: Var, f: Expr ): Stream[Expr] = {
      val constrs = enumerateTerms.forType( x.ty ).filter( _.ty == x.ty ).take( opts.sampleTestTerms )
      constrs.map( replaceExpr( f, x, _ ) )
    }

    def go( e: Expr ): Expr =
      e match {
        case Ex( x, f ) =>
          val tests = samples( x, f )
          tests.foldLeft( Bottom().asInstanceOf[Formula] )( ( acc, test ) => Or( acc, go( test ) ) )

        case All( x, f ) =>
          val tests = samples( x, f )
          tests.foldLeft( Top().asInstanceOf[Formula] )( ( acc, test ) => And( acc, go( test ) ) )

        case App( a, b ) => App( go( a ), go( b ) )
        case lhs         => lhs
      }

    go( e )
  }

  // We need to orient equalities the same way around for the SAT solver to treat them the same
  def orientEqualities( e: Expr ): Expr = {
    def go( e: Expr ): Expr =
      e match {
        case Eq( lhs, rhs ) =>
          val l = go( lhs )
          val r = go( rhs )
          if ( l.toRawAsciiString <= r.toRawAsciiString )
            Eq( l, r )
          else
            Eq( r, l )

        case App( a, b ) => App( go( a ), go( b ) )
        case lhs         => lhs
      }

    go( e )
  }

  // Tests expr by substituting small concrete terms for vars and normalizing the resulting expression.
  def testFormulaRaw( expr: Expr, vars: List[Var] )( implicit ctx: Context ): Boolean = {
    def go( e: Expr, subs: List[VarOrConst] ): Seq[Expr] = {
      subs match {
        case List() => Seq( e )
        case v :: vs =>
          val termStream = enumerateTerms.forType( v.ty )( ctx )
          val terms = termStream filter ( _.ty == v.ty ) take opts.sampleTestTerms
          terms.flatMap( t => go( e, vs ) map ( replaceExpr( _, v, t ) ) )
      }
    }

    val fs = go( expr, vars )

    def normalize( e: Expr ): Expr = orientEqualities( normalizer.normalize( unfoldQuantifiers( e ) ) )

    val origConstants = Context().constants.toSet
    def isNormalized( e: Expr ): Boolean = constants( e ).forall( c => origConstants.contains( c ) || isConstructor( c ) )

    def isValid( e: Expr ): Boolean = sat.isValid( e.asInstanceOf[Formula] )

    // Some terms, like `sk_0 == sk_0` do not reduce even though any instantiation of the skolem terms reduces
    // to the same value. Attempt to unblock such terms by testing for all constructor forms of the terms involved.
    def unblock( nf: Expr ): Boolean = {
      val skolems = constants( nf ).flatMap( asInductiveConst( _ )( ctx ) )

      if ( skolems.isEmpty )
        return false

      // Try to unblock overly specific reduction rules by casing on skolems
      val alts = skolems.foldLeft( Stream( nf ) ) {
        case ( ts, c ) =>
          val nConstrs = ctx.getConstructors( c.ty ).map( _.size ).getOrElse( 0 )
          val constrs = enumerateTerms.forType( c.ty ).filter( _.ty == c.ty ).take( nConstrs )
          ts.flatMap( t => constrs.map( s => replaceExpr( t, c, s ) ) )
      }

      alts.forall( alt => check( normalize( alt ) ).getOrElse( false ) )
    }

    // Returns Some( true ) if nf holds, Some( false ) if nf does not hold
    // and we have a normalised counter-example and None otherwise
    def check( nf: Expr ): Option[Boolean] =
      nf match {
        case Top()                               => Some( true )
        case Bottom()                            => Some( false )
        case _ if isValid( nf ) || unblock( nf ) => Some( true )
        case _ if isNormalized( nf )             => Some( false )
        case _                                   => None
      }

    val counters = fs.map( normalize ).filterNot { nf =>
      check( nf ).getOrElse( acceptNotNormalized || constants( nf ).exists( uninterpretedFun( _ )( ctx ) ) )
    }

    /*
    val msg = if ( counters.isEmpty ) "ACCEPTED" else "REJECTED"

    println( msg + ": " + expr )
    if ( counters.nonEmpty )
      println( "COUNTER: " + counters.head )
    println()
     */

    counters.isEmpty
  }

  def testFormula( expr: Expr, vars: List[Var] )( implicit ctx: Context ): Boolean = {
    if ( opts.sampleTestTerms == 0 )
      return true

    EscargotLogger.time( "testing" ) {
      testFormulaRaw( expr, vars )
    }
  }

  def uninterpretedFun( c: Const )( implicit ctx: Context ): Boolean =
    problem.uninterpretedConsts.contains( c ) && !isConstructor( c )

  // Given an expression, returns a triple:
  // 1: A map from subexpressions that occur in primary positions to those positions.
  // 2: A map from subexpressions that occur in passive positions to those positions.
  // 3: A set of subexpressions that occur in primary positions together directly under the same symbol.
  //  The sets are transitive, so if a and b occur together and b and c occur together, 3 will contain a set
  //  containing all of a, b and c.
  case class Occurences(
      primary:      Map[Expr, Seq[LambdaPosition]],
      accumulators: Map[Expr, Seq[LambdaPosition]],
      passive:      Map[Expr, Seq[LambdaPosition]],
      underSame:    Set[Set[Expr]] )

  def occurrences( formula: Expr )( implicit ctx: Context ): Occurences = {
    val empty = Seq.empty[( Expr, List[Int] )]

    def newPos( i: Int, size: Int, pos: List[Int] ): List[Int] =
      2 :: List.fill( size - i - 1 )( 1 ) ++ pos

    var underSame = Set.empty[Set[Expr]]

    def go( expr: Expr, pos: List[Int], inPrimary: Boolean ): ( Seq[( Expr, List[Int] )], Seq[( Expr, List[Int] )], Seq[( Expr, List[Int] )] ) =
      expr match {
        case Apps( c @ Const( _, _, _ ), rhsArgs ) =>
          if ( !allPositions.isDefinedAt( c ) && !uninterpretedFun( c )( ctx ) ) {
            rhsArgs.zipWithIndex.foldLeft( ( empty, empty, empty ) ) {
              case ( ( prim, accs, pass ), ( e, i ) ) =>
                val p = newPos( i, rhsArgs.size, pos )
                val ( l, m, r ) = go( e, newPos( i, rhsArgs.size, pos ), inPrimary )
                ( l ++ prim, m ++ accs, r ++ pass )
            }
          } else {
            val ( primaryArgs: Set[Int], accumulatorArgs: Set[Int], passiveArgs: Set[Int] ) =
              allPositions.get( c )
                .map( pos => ( pos.primaryArgs, pos.accumulatorArgs, pos.passiveArgs ) )
                .getOrElse( rhsArgs.zipWithIndex.map( _._2 ).toSet, Set(), Set() )

            /*
          allPositions.get( c ) match {
            case None =>
              rhsArgs.zipWithIndex.foldLeft( ( empty, empty, empty ) ) {
                case ( ( prim, accs, pass ), ( e, i ) ) =>
                  val p = newPos( i, rhsArgs.size, pos )
                  val ( l, m, r ) = go( e, newPos( i, rhsArgs.size, pos ), inPrimary )
                  ( ( e, p ) +: ( l ++ prim ), m ++ accs, r ++ pass )
              }
            case Some( positions ) =>
           */
            val pass1 = passiveArgs.toSeq flatMap { i =>
              val p = newPos( i, rhsArgs.size, pos )
              val ( l, m, r ) = go( rhsArgs( i ), p, inPrimary = false )
              ( rhsArgs( i ), p ) +: ( l ++ m ++ r )
            }

            val accs1 = accumulatorArgs.toSeq flatMap { i =>
              val p = newPos( i, rhsArgs.size, pos )
              val ( l, m, _ ) = go( rhsArgs( i ), p, inPrimary = false )
              ( rhsArgs( i ), p ) +: ( l ++ m )
            }

            if ( inPrimary ) {
              val directSame = primaryArgs map rhsArgs

              def collectNestedSame( exprs: Set[Expr] ): Set[Expr] = {
                exprs.flatMap {
                  case Apps( d @ Const( _, _, _ ), nestedArgs ) if c == d =>
                    val here = primaryArgs map nestedArgs
                    val there = collectNestedSame( here )
                    here ++ there
                  case _ => List()
                }
              }

              val same = directSame ++ collectNestedSame( directSame )

              // If any of the ones we just found, appear in another cluster, we should merge that cluster and this one
              underSame.filter( _.intersect( same ).nonEmpty ) match {
                case Seq() => underSame += same
                case existings =>
                  existings foreach {
                    underSame -= _
                  }
                  // The current expr may be in one of the clusters, so remove it as it is replaced by subterms
                  underSame += existings.foldLeft( same ) { case ( acc, set ) => acc union set } - expr
              }
            }

            val ( prim1, accs2, pass2 ) = primaryArgs.toSeq.foldLeft( ( empty, empty, empty ) ) {
              case ( ( prim, accs, pass ), i ) =>
                val p = newPos( i, rhsArgs.size, pos )
                val ( l, m, r ) = go( rhsArgs( i ), p, inPrimary )
                ( ( rhsArgs( i ), p ) +: ( l ++ prim ), m ++ accs, r ++ pass )
            }
            ( prim1, accs1 ++ accs2, pass1 ++ pass2 )
          }
        case App( a, b ) =>
          val ( l1, m1, r1 ) = go( a, 1 :: pos, inPrimary )
          val ( l2, m2, r2 ) = go( b, 2 :: pos, inPrimary )
          ( l1 ++ l2, m1 ++ m2, r1 ++ r2 )
        case _ => ( Seq(), Seq(), Seq() )
      }

    val ( prim, accs, pass ) = go( formula, List(), inPrimary = true )

    val primMap = prim.groupBy( _._1 ).mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse ) } )
    val accsMap = accs.groupBy( _._1 ).mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse ) } )
    val passMap = pass.groupBy( _._1 ).mapValues( seq => seq.map { case ( _, pos ) => LambdaPosition( pos.reverse ) } )

    Occurences( primMap, accsMap, passMap, underSame )
  }

  // Given a term c to induct over in f, returns a fresh induction variable
  // and a prioritized list of induction goals, the first more general than the next.
  def getTargets( c: Expr, f: Expr, occs: Occurences ): ( Var, Seq[Expr] ) = {
    val primPoses = occs.primary.getOrElse( c, Seq() )
    val passPoses = occs.passive.getOrElse( c, Seq() )
    val v = Var( nameGen.fresh( "ind" ), c.ty )

    var targets = List( replaceExpr( f, c, v ) )

    if ( opts.performGeneralization && primPoses.size >= 2 && passPoses.nonEmpty ) {
      // Induct only on primary occurences, i.e. generalize
      targets ::= primPoses.foldLeft( f )( ( g, pos ) => g.replace( pos, v ) )
    }

    ( v, targets )
  }

  def quantifyAccumulators( f: Expr, occs: Occurences )( implicit ctx: Context ): Expr = {
    val accsPoses = occs.accumulators.filterKeys( asInductiveConst( _ )( ctx ).isDefined )

    accsPoses.foldLeft( f ) {
      case ( g, ( acc, _ ) ) =>
        val w = Var( nameGen.fresh( "ind" ), acc.ty )
        All( w, replaceExpr( g, acc, w ) )
    }
  }

  def universalClosureExcept( f: Formula, vars: Set[Var] ): Formula =
    ( variables( f ) -- vars ).foldLeft( f ) { case ( g, x ) => All( x, g ) }

  def clauseAxioms( cls: HOLSequent )( implicit ctx: MutableContext ): Seq[Axiom] = {
    val f = negate( cls.toFormula ).asInstanceOf[Expr]
    val occs = occurrences( f )( ctx )

    val underSame = occs.underSame.map( _.filter { t =>
      asInductiveConst( t )( ctx ).isDefined ||
        // Only generalise function-headed subterms with at least two primary occurences
        ( opts.performGeneralization && funHeaded( t ) && occs.primary( t ).size >= 2 )
    } )

    underSame.toSeq.flatMap {
      case ts if ts.isEmpty => Seq()
      case ts if ts.size == 1 =>
        // This term only appears alone in primary position, so we do a regular induction on it.
        val t = ts.head
        // Passing in the same occurrences is okay, as we only change proper subterms
        val ( v, targets ) = getTargets( t, f, occs )

        // If we accept non-normalized terms, we may accept a too-general target and miss the actual one,
        // so use filter in that case to get all of them. This only occurs when lambdas are in play.
        def findOrFilter( f: Expr => Boolean ): Seq[Expr] =
          if ( acceptNotNormalized ) targets.filter( f ) else targets.find( f ).toSeq

        findOrFilter( testFormula( _, List( v ) )( ctx ) ) flatMap { targ =>
          val target = universalClosureExcept( quantifyAccumulators( targ, occs ).asInstanceOf[Formula], Set( v ) )
          StandardInductionAxioms( v, target )( ctx ).toOption.map( Seq( _ ) )
        }
      case ts =>
        // These terms appear together so we need to induct on all of them together for the definitions to reduce.
        // For each of them, we might need to generalize passive occurrences, so we calculate a sequence of less and
        // less general formulas to be tested.

        def buildTargets( ts: Set[Expr] ): Seq[( Seq[Var], Expr )] = {
          ts.foldLeft( Seq( ( Seq.empty[Var], f ) ) ) {
            case ( vsfs, t ) =>
              vsfs.flatMap {
                case ( vs, g ) =>
                  val ( v, ts ) = getTargets( t, g, occs )
                  ts map ( ( v +: vs, _ ) )
              }
          }
        }

        // Also generate targets where we don't generalise subterms, in case all of those fail tests.
        val targets = buildTargets( ts ) ++ buildTargets( ts.flatMap( asInductiveConst( _ )( ctx ) ) )

        targets.find { case ( vs, target ) => testFormula( target, vs.toList )( ctx ) } flatMap {
          case ( vs, targ ) =>
            val target = universalClosureExcept( quantifyAccumulators( targ, occs ).asInstanceOf[Formula], vs.toSet )
            SequentialInductionAxioms()( Sequent() :+ ( "axiom", target.asInstanceOf[Formula] ) )( ctx ).toOption
        }
    } flatten
  }

}

