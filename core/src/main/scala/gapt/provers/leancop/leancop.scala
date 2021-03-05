package gapt.provers.leancop

import gapt.expr.formula.And
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.hol.removeAllQuantifiers

import java.io.IOException
import java.io.StringReader
import gapt.expr.formula.hol.universalClosure
import gapt.expr.formula.{ All, Atom, Eq, Neg, Or }
import gapt.expr.subst.FOLSubstitution
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.formats.leancop.LeanCoPLeanPredWrongArityException
import gapt.formats.leancop.LeanCoPNoMatchException
import gapt.formats.leancop.LeanCoPParser.LeanCoPClause
import gapt.formats.leancop.LeanCoPParser.ClauseIndex
import gapt.formats.leancop.LeanCoPParser.FOLLiteral
import gapt.formats.leancop.LeanCoPParser.InputFormula
import gapt.formats.leancop.LeanCoPParser.LeanInstance
import gapt.formats.leancop.LeanCoPParser.LeanPredicate
import gapt.formats.leancop.LeanCoPParser.LeanProof
import gapt.formats.leancop.LeanCoPParser.Name
import gapt.formats.leancop.LeanCoPParser.Role
import gapt.formats.leancop.{ LeanCoP21Parser, LeanCoPParser }
import gapt.proofs.expansion.{ ETWeakQuantifierBlock, ExpansionProof, ExpansionProofToLK, ExpansionSequent, formulaToExpansionTree }
import gapt.formats.tptp.TptpFOLExporter
import gapt.logic.hol.DNFp
import gapt.logic.hol.toNNF
import gapt.logic.{ Polarity, clauseSubsumption }
import gapt.proofs.FOLClause
import gapt.proofs.{ Clause, HOLClause, HOLSequent, Sequent }
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionToExpansionProof
import gapt.proofs.resolution.expansionProofFromInstances
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.OneShotProver
import gapt.provers.renameConstantsToFi
import gapt.utils.EitherHelpers._
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess
import gapt.utils.withTempFile

import scala.collection.mutable

object LeanCoP extends LeanCoP
class LeanCoP extends OneShotProver with ExternalProgram {
  private val nLine = sys.props( "line.separator" )

  override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
    getExpansionProof( s )( ctx.map( _.newMutable ) ).isDefined

  override def getExpansionProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    val cnf = structuralCNF( s ).map( c => universalClosure( c.conclusion.toDisjunction ) -> c ).toMap
    // LeanCoP doesn't like empty clauses
    for ( ( _, clause ) <- cnf if clause.isProof ) return Some( ResolutionToExpansionProof( clause ) )

    renameConstantsToFi.wrap( cnf.keys ++: Sequent() )( ( renaming, sequent: HOLSequent ) => {
      val tptp = TptpFOLExporter( sequent ).toString
      val ( exitValue, stdout ) = withTempFile.fromString( tptp ) { leanCoPInput =>
        runProcess.withExitValue( Seq( "leancop", leanCoPInput.toString ) )
      }
      if ( exitValue == 1 && stdout.contains( "is Satisfiable" ) ) {
        None
      } else if ( exitValue == 0 ) {
        if ( stdout.contains( "%-" ) ) { // LeanCop TPTP format
          // extract the part between the %----- delimiters
          val tptpProof = stdout.split( nLine ).
            dropWhile( !_.startsWith( "%-" ) ).drop( 1 ).
            takeWhile( !_.startsWith( "%-" ) ).
            mkString( nLine )
          val leanProof = LeanCoPParser.parseLeanProof( new StringReader( tptpProof ) )
          Some( leanCoPProofToExpansionSequent( leanProof ) )
        } else { // LeanCoP 2.1 format (only compact atm)
          val Right( connPrf ) = LeanCoP21Parser.parse( stdout )

          val clauses = connPrf.toFOLClauses.map( _.swapped )
          Some( sequent.map {
            case fml @ All.Block( _, Or.nAry( lits ) ) =>
              val cls = Clause( lits.collect { case Neg( a: Atom ) => a }, lits.collect { case a: Atom => a } )
              formulaToExpansionTree(
                fml,
                for { inst <- clauses; subst <- clauseSubsumption( cls, inst ) } yield subst,
                Polarity.InAntecedent )
          } )
        }
      } else {
        throw new IllegalArgumentException( s"Unexpected leancop output with exit value ${exitValue}:\n${stdout}" )
      }
    } ).map {
      case es =>
        val hasEquality = cnf.values.flatMap( _.conclusion.elements ).exists {
          case Eq( _, _ ) => true
          case _          => false
        }

        val substs = for {
          ETWeakQuantifierBlock( shallow, _, insts ) <- es.elements
          ( formula @ All.Block( vars, _ ), clause ) <- cnf
          if formula == shallow
        } yield clause.conclusion.asInstanceOf[HOLClause] ->
          insts.keys.map( s => Substitution( vars zip s ) ).toSet

        expansionProofFromInstances( substs.toMap, cnf.values.toSet, !hasEquality )
    }
  }

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    getExpansionProof( seq ) map { ExpansionProofToLK( _ ).get }

  override val isInstalled: Boolean = try runProcess.withExitValue( Seq( "leancop" ) )._1 == 2
  catch { case _: IOException => false }
}

object leanCoPProofToExpansionSequent {

  def apply( p: LeanProof ): ExpansionSequent =
    constructExpansionSequent(
      p.initialFormulas.toList,
      p.clauses.toList,
      p.instances.toList )

  private def constructExpansionSequent(
    inputs:   List[InputFormula],
    clauses:  List[LeanCoPClause],
    bindings: List[LeanInstance] ): ExpansionSequent = {

    val initialFormula: Map[Name, InputFormula] =
      ( inputs ++
        clauses.collect {
          case LeanCoPClause( i, f, n @ "lean_eq_theory" ) => InputFormula( n + "_" + i, "axiom", f.toConjunction )
        } ).map { i => i.name -> i } toMap

    val derivedClauses: List[LeanCoPClause] =
      clauses.filter { _.origin != "lean_eq_theory" }

    val children: Map[Name, Iterable[LeanCoPClause]] =
      derivedClauses.groupBy( _.origin )

    val substitutions: Map[ClauseIndex, List[FOLSubstitution]] =
      bindings.groupMap( _.index )( _.substitution )

    // Instances of the original formula of the given name.
    val instances: Map[Name, List[FOLSubstitution]] =
      children map {
        case ( name, lst_int ) =>
          val leanClauses = lst_int.map( _.cls ).toList
          // New predicates used in the def clausal translation and arity
          val leanPredicates = leanClauses.flatMap( c => getLeanPreds( c ) ).distinct
          val f_clausified = clausifyInitialFormula( initialFormula( name ), leanPredicates )
          val subs = matchClauses( f_clausified, leanClauses ) match {
            case Some( s ) => s
            case None => throw new LeanCoPNoMatchException( "leanCoP parsing: formula " + f_clausified +
              " and clauses " + leanClauses + " do not match." )
          }
          val sublst = lst_int.flatMap( i => substitutions.get( i.index ) match {
            case Some( cs ) => cs.map( s => s.compose( subs ) )
            case None       => List( subs )
          } ).toList
          name -> sublst
      }
    val polarizedETs = instances.map {
      case ( name, sublst ) =>
        val f = initialFormula( name )
        val p = polarityByRole( f.role )
        formulaToExpansionTree( f.formula, sublst, p ) -> p
    }
    ExpansionSequent( polarizedETs )
  }

  /**
   * Clausifies the given formula.
   *
   * The clausification makes use of the predicate symbols introduced by LeanCoP.
   */
  def clausifyInitialFormula( f: InputFormula, leanPredicates: List[LeanPredicate] ): List[FOLClause] = {
    val InputFormula( _, role, f_original ) = f
    val f_right_pol =
      if ( role == "conjecture" ) f_original
      else Neg( f_original )
    val f_in_nnf = toNNF( f_right_pol )
    val f_no_quant = removeAllQuantifiers( f_in_nnf )
    // If there are not lean predicate symbols, use regular DNF transformation
    leanPredicates match {
      case Seq() => toMagicalDNF( f_no_quant )
      case _     => toDefinitionalClausalForm( f_no_quant, leanPredicates )
    }
  }

  def toMagicalDNF( f: FOLFormula ): List[FOLClause] = {
    DNFp( f ).toList
  }

  /**
   * Computes the definitional clausal form of a given formula.
   *
   * @param f The formula in NNF whose DCF is to be constructed.
   * @param leanPredicates The predicates available for the DCF construction.
   * @return A list list of clauses in DNF (possibly with introduced definitions) corresponding to the
   *         definitional clausal form of the input formula
   */
  def toDefinitionalClausalForm( f: FOLFormula, leanPredicates: List[LeanPredicate] ): List[FOLClause] = {

    type DefinitionalTuple = ( FOLFormula, List[FOLFormula] )

    var unusedPredicates: mutable.Set[LeanPredicate] = mutable.Set( leanPredicates: _* )

    def definitionalTuple( f: FOLFormula, insideConjunction: Boolean ): DefinitionalTuple =
      f match {
        case FOLLiteral( _, _ ) => ( f, List() )
        case Or( f1, f2 ) if insideConjunction => {
          val xs = freeVariables( f )
          getUnusedPredicate( xs.size ) match {
            case Some( p ) =>
              // Trusting that we have the same order as leanCoP
              val pxs = FOLAtom( p._1, xs.toList )
              unusedPredicates -= p
              val ( f1d, d1 ) = definitionalTuple( f1, insideConjunction )
              val ( f2d, d2 ) = definitionalTuple( f2, insideConjunction )
              ( pxs, ( -pxs & f1d ) :: ( -pxs & f2d ) :: d1 ++ d2 )
            case _ => throw new LeanCoPLeanPredWrongArityException(
              "Formula: " + f + " Candidates: " + unusedPredicates + " Arity: " + xs.size )
          }
        }
        case And( f1, f2 ) =>
          val ( f1d, d1 ) = definitionalTuple( f1, true )
          val ( f2d, d2 ) = definitionalTuple( f2, true )
          ( And( f1d, f2d ), d1 ++ d2 )
        case Or( f1, f2 ) =>
          val ( f1d, d1 ) = definitionalTuple( f1, insideConjunction )
          val ( f2d, d2 ) = definitionalTuple( f2, insideConjunction )
          ( Or( f1d, f2d ), d1 ++ d2 )
        case _ => throw new Exception( "Unsupported format for definitional clausal transformation: " + f )
      }

    /*
     * Retrieves a currently unused predicate of the given arity.
     * @param n The arity of the predicate.
     */
    def getUnusedPredicate( n: Int ): Option[LeanPredicate] =
      unusedPredicates.collectFirst { case p @ ( _, `n` ) => p }

    val ( fd, defs ) = definitionalTuple( f, false )
    DNFp( fd ) ++ defs.flatMap( d => DNFp( d ) ) toList
  }

  /**
   * Tries to match our clauses with the corresponding LeanCoP clauses.
   *
   * @param myClauses DNFp clauses
   * @param leanClauses DNFp clauses
   * @return A
   */
  def matchClauses( myClauses: List[FOLClause], leanClauses: List[FOLClause] ): Option[FOLSubstitution] = {

    def findSubstitution( lst: List[List[FOLClause]], goal: List[FOLClause] ): Option[FOLSubstitution] = lst match {
      case Nil => None
      case hd :: tl => clauseSubsumption( hd.head, goal.head ) match {
        case None        => findSubstitution( tl, goal )
        case Some( sub ) => Some( sub.asFOLSubstitution )
      }
    }

    val candidates = myClauses.combinations( leanClauses.length ).flatMap( s => s.permutations )

    findSubstitution( candidates.toList, leanClauses )
  }

  // Collects all n ^ [...] predicates used and their arities
  def getLeanPreds( cls: FOLFormula ): List[( String, Int )] = cls match {
    case FOLAtom( n, args ) if n.startsWith( "leanP" ) => List( ( n, args.length ) )
    case FOLAtom( _, _ ) => List()
    case Neg( f ) => getLeanPreds( f )
    case And( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case Or( f1, f2 ) => getLeanPreds( f1 ) ++ getLeanPreds( f2 )
    case _ => throw new Exception( "Unsupported format for getLeanPreds: " + cls )
  }

  def getLeanPreds( c: FOLClause ): List[( String, Int )] =
    ( c.antecedent ++ c.succedent ).flatMap( getLeanPreds ).toList

  def polarityByRole( r: Role ): Polarity =
    r match {
      case "axiom" => Polarity.InAntecedent
      case _       => Polarity.InSuccedent
    }
}

