package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.hol.lcomp
import gapt.proofs.rup._
import gapt.proofs.lk._
import gapt.proofs._
import gapt.provers.congruence.CC
import gapt.provers.escargot.Escargot
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs._
import gapt.provers.sat.Sat4j._
import gapt.utils.{ generatedUpperSetInPO, quiet }
import org.sat4j.core.VecInt
import org.sat4j.tools.SearchListenerAdapter

import scala.annotation.tailrec
import scala.collection.mutable

class ExpansionProofToMG3iViaSAT( val expansionProof: ExpansionProof ) {
  val solver = SolverFactory.newDefault()
  def newVar(): Int = solver.nextFreeVarId( true )

  implicit def clause2sat4j( clause: Iterable[Int] ): IVecInt =
    new VecInt( clause.toArray )
  implicit def sat4j2clause_( clause: IVecInt ): Set[Int] =
    clause.toArray.toSet

  val shAtoms = expansionProof.subProofs.
    map( _.shallow ).
    toSeq.sortBy( lcomp( _ ) ).
    map( sh => sh -> newVar() ).
    toMap
  def atom( f: Formula ): Int = shAtoms( f )
  def atom( e: ExpansionTree ): Int = atom( e.shallow )

  val atomToSh = shAtoms.map( _.swap )
  val atomToET = expansionProof.subProofs.groupBy( atom ).withDefaultValue( Set() )

  def modelSequent( lits: Traversable[Int] ): HOLSequent =
    Sequent( lits.flatMap( l => atomToSh.get( math.abs( l ) ).map( _ -> Polarity( l < 0 ) ) ) )
  def implication( lits: Traversable[Int] ): HOLSequent =
    modelSequent( lits ).swapped
  def expSeq( lits: Traversable[Int] ): ExpansionSequent =
    Sequent( lits.flatMap( l => atomToET( math.abs( l ) ).map( e => e -> e.polarity ) ) )

  val drup = mutable.Buffer[RupProof.Line]()
  solver.setSearchListener( new SearchListenerAdapter[ISolverService] {
    override def learnUnit( p: Int ) = drup += RupProof.Rup( Set( p ) )
    override def learn( c: IConstr ) = drup += RupProof.Rup( c )
  } )

  val proofs = mutable.Map[Set[Int], Either[LKProof, ( Set[Int], LKProof => LKProof )]]()
  def clause( seq: HOLSequent ): Seq[Int] = seq.map( -atom( _ ), atom ).elements
  def addClause( p: LKProof ): Unit = addClause( p, p.endSequent )
  def addClause( p: LKProof, seq: HOLSequent ): Unit = {
    val cls = clause( seq ).toSet
    if ( !proofs.contains( cls ) ) {
      proofs( cls ) = Left( p )
      drup += RupProof.Input( cls )
      solver.addClause( cls )
    }
  }
  def addClause( lower: HOLSequent, upper: HOLSequent )( p: LKProof => LKProof ): Unit = {
    val lowerC = clause( lower ).toSet
    val upperC = clause( upper ).toSet
    if ( !proofs.contains( lowerC ) ) {
      require( !solver.isSatisfiable( upperC.map( -_ ) ) )
      drup += RupProof.Rup( upperC )
      proofs( lowerC ) = Right( ( upperC, p ) )
      drup += RupProof.Input( lowerC )
      solver.addClause( lowerC )
    }
  }

  val classical = newVar()

  expansionProof.subProofs.foreach {
    case ETWeakening( _, _ )              =>
    case ETMerge( _, _ ) | ETAtom( _, _ ) => // implicit because shallow formulas are the same
    case ETTop( _ )                       => addClause( TopAxiom )
    case ETBottom( _ )                    => addClause( BottomAxiom )
    case ETAnd( a, b ) =>
      addClause( AndLeftMacroRule( LogicalAxiom( a.shallow ), a.shallow, b.shallow ) )
      addClause( AndLeftMacroRule( LogicalAxiom( b.shallow ), a.shallow, b.shallow ) )
      addClause( AndRightRule( LogicalAxiom( a.shallow ), Suc( 0 ), LogicalAxiom( b.shallow ), Suc( 0 ) ) )
    case ETOr( a, b ) =>
      addClause( OrLeftRule( LogicalAxiom( a.shallow ), Ant( 0 ), LogicalAxiom( b.shallow ), Ant( 0 ) ) )
      addClause( OrRightMacroRule( LogicalAxiom( a.shallow ), a.shallow, b.shallow ) )
      addClause( OrRightMacroRule( LogicalAxiom( b.shallow ), a.shallow, b.shallow ) )
    case e @ ETWeakQuantifier( sh, insts ) =>
      for ( ( inst, a ) <- insts ) addClause {
        if ( e.polarity.inSuc ) ExistsRightRule( LogicalAxiom( a.shallow ), sh, inst )
        else ForallLeftRule( LogicalAxiom( a.shallow ), sh, inst )
      }
    case e @ ETNeg( a ) =>
      addClause( NegLeftRule( LogicalAxiom( a.shallow ), a.shallow ) )
      solver.addClause( Seq( -classical, atom( a.shallow ), atom( e.shallow ) ) )
    case e @ ETImp( a, b ) =>
      addClause( ImpLeftRule( LogicalAxiom( a.shallow ), Suc( 0 ), LogicalAxiom( b.shallow ), Ant( 0 ) ) )
      addClause( ImpRightMacroRule( LogicalAxiom( b.shallow ), a.shallow, b.shallow ) )
      solver.addClause( Seq( -classical, atom( e.shallow ), atom( a.shallow ) ) )
    case e @ ETStrongQuantifier( sh, ev, ch ) =>
      if ( e.polarity.inSuc )
        addClause( ForallLeftRule( LogicalAxiom( ch.shallow ), Ant( 0 ), sh, ev ) )
      else
        addClause( ExistsRightRule( LogicalAxiom( ch.shallow ), Suc( 0 ), sh, ev ) )
      val pol = if ( e.polarity.inSuc ) 1 else -1
      solver.addClause( Seq( -classical, -pol * atom( ch.shallow ), pol * atom( e.shallow ) ) )
    case ETDefinition( sh, ch ) =>
      addClause( DefinitionRightRule( LogicalAxiom( ch.shallow ), ch.shallow, sh ) )
      addClause( DefinitionLeftRule( LogicalAxiom( ch.shallow ), ch.shallow, sh ) )
    case ETSkolemQuantifier( _, _, _ ) => throw new IllegalArgumentException
  }

  val clausificationClauses = drup.toVector

  val cc = CC().intern( shAtoms.keys.filter( _.isInstanceOf[Atom] ) )
  val hasEquality = shAtoms.keys.exists { case Eq( _, _ ) => true case _ => false }
  @tailrec final def isESatisfiable( assumptions: IVecInt ): Boolean =
    if ( !solver.isSatisfiable( assumptions ) ) false
    else if ( !hasEquality ) true
    else cc.mergeAndExplain( modelSequent( solver.model() ).
      collect { case a: Atom => a } ) match {
      case Some( core ) =>
        val Some( p ) = quiet( Escargot.getAtomicLKProof( core ) )
        addClause( p )
        isESatisfiable( assumptions )
      case None =>
        true
    }

  val dependencies = Map() ++ ( for ( ev <- expansionProof.eigenVariables )
    yield ev -> ( generatedUpperSetInPO( List( ev ), expansionProof.dependencyRelation.map( _.swap ) ) - ev ) )
  val immediateDeps = for ( ( ev1, down1 ) <- dependencies )
    yield ev1 -> ( down1 -- down1.flatMap( dependencies ) )
  val noReverseDeps = expansionProof.eigenVariables -- expansionProof.dependencyRelation.map( _._1 )

  val atomsWithFreeVar: Map[Var, Set[Int]] =
    Map().withDefaultValue( Set.empty[Int] ) ++
      atomToSh.view.flatMap { case ( a, f ) => freeVariables( f ).map( _ -> a ) }.
      groupBy( _._1 ).mapValues( _.map( _._2 ).toSet )

  type Counterexample = Set[Int] // just the assumptions
  type Result = Either[Counterexample, Unit]

  val unprovable = mutable.Buffer[( Set[Var], Counterexample )]()

  def refute( eigenVariables: Set[Var], model: Vector[Int] ): Result = {
    def minimizeCtx( ctx: Set[Int], upper: Set[Int] ): Set[Int] = {
      def go( todo: List[Int], ctx: Set[Int] ): Set[Int] =
        todo match {
          case t :: ts if !solver.isSatisfiable( upper union ( ctx - t ) ) => go( ts, ctx - t )
          case _ :: ts => go( ts, ctx )
          case Nil => ctx
        }
      require( !solver.isSatisfiable( upper union ctx ) )
      val ctx_ = ctx.intersect( solver.unsatExplanation() )
      go( ctx_.toList.sortBy( -math.abs( _ ) ), ctx_ )
    }
    def addClauseWithCtx( ctx: Set[Int], upper: Set[Int], lower: Set[Int] )( p: LKProof => LKProof ): Unit =
      if ( solver.isSatisfiable( ctx ) ) {
        val ctx2 = minimizeCtx( ctx, upper )
        addClause( upper = modelSequent( upper ++ ctx2 ), lower = modelSequent( lower ++ ctx2 ) )( p )
      }

    def tryExistsLeft(): Option[Result] =
      model.view.filter( _ > 0 ).flatMap( atomToET ).flatMap {
        case e @ ETStrongQuantifier( sh, ev, a ) if e.polarity.inAnt &&
          !eigenVariables.contains( ev ) =>
          val atomsWithEV = atomsWithFreeVar( ev )
          val ctx = model.view.filter( a => !atomsWithEV.contains( math.abs( a ) ) ).toSet
          val provable = solve( eigenVariables + ev, ctx + atom( a ) )
          if ( provable.isRight ) addClauseWithCtx( ctx, Set( atom( a ) ), Set( atom( e ) ) )( p =>
            if ( !p.endSequent.antecedent.contains( a.shallow ) ) p
            else ExistsLeftRule( p, sh, ev ) )
          Some( provable ).filter( _.isRight || dependencies( ev ).subsetOf( eigenVariables ) )
        case _ => None
      }.headOption

    def tryNonInvertible(): Option[Result] = {
      def handleBlock( e: ExpansionTree, upper: Set[Int], eigenVariables: Set[Var],
                       back: LKProof => LKProof ): ( Set[Int], Set[Var], LKProof => LKProof ) =
        e match {
          case ETNeg( a ) =>
            ( upper + atom( a ), eigenVariables, p =>
              back( if ( !p.endSequent.antecedent.contains( a.shallow ) ) p else
                NegRightRule( p, a.shallow ) ) )
          case ETImp( a, b ) =>
            handleBlock( b, upper + atom( a ), eigenVariables, p => back(
              if ( !p.endSequent.antecedent.contains( a.shallow ) && !p.endSequent.succedent.contains( b.shallow ) ) p else
                ImpRightMacroRule( p, a.shallow, b.shallow ) ) )
          case ETStrongQuantifier( _, ev, a ) =>
            handleBlock( a, upper, eigenVariables + ev, p => back(
              if ( !p.endSequent.succedent.contains( a.shallow ) ) p else
                ForallRightRule( p, e.shallow, ev ) ) )
          case _ =>
            ( upper + -atom( e ), eigenVariables, back )
        }
      val candidates = model.view.filter( _ < 0 ).map( -_ ).flatMap( atomToET ).collect {
        case e @ ETNeg( a ) if e.polarity.inSuc && !model.contains( atom( a ) )    => e
        case e @ ETImp( a, _ ) if e.polarity.inSuc && !model.contains( atom( a ) ) => e
        case e @ ETStrongQuantifier( _, ev, _ ) if e.polarity.inSuc
          && !eigenVariables.contains( ev ) => e
      }
      val nextSteps = candidates.map { e =>
        val ( upper, newEvs, transform ) = handleBlock( e, Set.empty, Set.empty, identity )
        val atomsWithEigenVars = newEvs.flatMap( atomsWithFreeVar )
        val ctx = model.view.filter( _ > 0 ).toSet.diff( atomsWithEigenVars )
        ( upper, Set( -atom( e ) ), ctx, newEvs, transform )
      }
      nextSteps.find {
        case ( upper, _, ctx, newEvs, _ ) =>
          solve( eigenVariables ++ newEvs, ctx ++ upper ).isRight
      } match {
        case Some( ( upper, lower, ctx, _, transform ) ) =>
          addClauseWithCtx( ctx, upper, lower )( transform )
          Some( Right( () ) )
        case None =>
          None
      }
    }

    tryExistsLeft().orElse( tryNonInvertible() ).getOrElse( Left( model.toSet ) ) match {
      case ok @ Right( _ ) => // next model
        require( !solver.isSatisfiable( model ) )
        ok
      case reason @ Left( _ ) =>
        if ( solver.isSatisfiable( model ) ) {
          unprovable += ( ( eigenVariables, model.toSet ) )
          reason
        } else {
          // We solved the current goal even though no ∃:l, ∀:r, →:r, ¬:r rule was successful.
          // This can happen if we learned a useful lemma during the search.
          Right( () )
        }
    }
  }

  def solve( eigenVariables: Set[Var], assumptions: Set[Int] ): Result = {
    unprovable.find {
      case ( evs, ass ) => evs.subsetOf( eigenVariables ) && assumptions.subsetOf( ass )
    } match {
      case Some( ( _, ass ) ) =>
        return Left( ass )
      case _ =>
    }

    if ( isESatisfiable( assumptions + classical ) )
      return Left( assumptions )

    while ( isESatisfiable( assumptions ) ) {
      val model = solver.model().view.filter( v => v != classical && v != -classical ).toVector

      refute( eigenVariables, model ) match {
        case reason @ Left( _ ) => return reason
        case Right( _ )         => // next model
      }
    }
    Right( () )
  }

  def solve(): Either[HOLSequent, LKProof] =
    ( try {
      for ( e <- expansionProof.expansionSequent.antecedent )
        addClause( LogicalAxiom( e.shallow ), Sequent() :+ e.shallow )
      solve( Set(), expansionProof.expansionSequent.succedent.map( -atom( _ ) ).toSet )
    } catch {
      case _: ContradictionException =>
        Right( () )
    } ) match {
      case Left( reason ) =>
        require( solver.isSatisfiable( reason + ( -classical ) ) )
        val model = solver.model().toSet

        val solver2 = SolverFactory.newDefault()
        solver2.newVar( solver.nVars() )
        for ( RupProof.Input( cls ) <- clausificationClauses )
          solver2.addClause( cls )

        def minimize( ls: List[Int], done: List[Int] ): List[Int] =
          ls match {
            case l :: ls_ =>
              if ( !solver2.isSatisfiable( ( -l ) :: done ) )
                minimize( ls_, done )
              else
                cc.mergeAndExplain( modelSequent( solver2.model() ).collect { case a: Atom => a } ) match {
                  case Some( core ) =>
                    solver2.addClause( clause( core ) )
                    minimize( ls, done )
                  case None =>
                    minimize( ls_, l :: done )
                }
            case Nil => done
          }

        Left( modelSequent( minimize( model.toList.sortBy( l => math.abs( l ) ), Nil ) ) )
      case Right( () ) =>
        val goal = clause( expansionProof.expansionSequent.shallow ).toSet
        val drupP = RupProof( ( drup :+ RupProof.Rup( goal ) ).
          filterNot( _.clause.contains( -classical ) ) )
        val replayed = ( drupP.lines.map( _.clause ) zip drupP.toResProofs ).reverse.toMap
        def toLK( clause: Set[Int] ): LKProof =
          replayed( clause ).toLK( atomToSh, cls => proofs( cls ) match {
            case Left( p ) => p
            case Right( ( upper, f ) ) =>
              WeakeningMacroRule( f( toLK( upper ) ), implication( cls ), strict = false )
          } )
        val lk = toLK( goal )
        Right( lk )
    }
}

object ExpansionProofToMG3iViaSAT {
  def apply( f: Formula ): Either[( Unit, HOLSequent ), LKProof] =
    apply( Sequent() :+ f )

  def apply( seq: HOLSequent ): Either[( Unit, HOLSequent ), LKProof] =
    apply( ExpansionProof( formulaToExpansionTree( seq ) ) )

  def apply( exp: ExpansionProof ): Either[( Unit, HOLSequent ), LKProof] =
    new ExpansionProofToMG3iViaSAT( exp ).solve().left.map( () -> _ )
}
