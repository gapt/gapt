package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.gapt.proofs._

import scala.App

/**
 * Created by sebastian on 10/12/15.
 */
object DefinitionElimination extends DefinitionElimination
class DefinitionElimination extends at.logic.gapt.utils.logging.Logger {
  type DefinitionsMap = Map[LambdaExpression, LambdaExpression]
  type ProcessedDefinitionsMap = Map[SymbolA, ( List[Var], HOLFormula )]

  /**
   * Eliminates definitions in a HOLFormula.
   *
   * @param dmap A DefinitionsMap.
   * @param f A HOLFormula.
   * @return f with all definitions in dmap eliminated.
   */
  def apply( dmap: DefinitionsMap, f: HOLFormula ): HOLFormula = {
    val edmap = expand_dmap( dmap )
    BetaReduction.betaNormalize( replaceAll_informula( edmap, f ) )
  }

  /**
   * Eliminates definitions in a LambdaExpression.
   *
   * @param dmap A DefinitionsMap.
   * @param f A LambdaExpression.
   * @return f with all definitions in dmap eliminated.
   */
  def apply( dmap: DefinitionsMap, f: LambdaExpression ): LambdaExpression = {
    val edmap = expand_dmap( dmap )
    BetaReduction.betaNormalize( replaceAll_in( edmap, f ) )
  }

  /**
   * Eliminates definitions in an LKProof.
   *
   * @param dmap A DefinitionsMap.
   * @param p An LKProof.
   * @return p with all definitions in dmap eliminated.
   */
  def apply( dmap: DefinitionsMap, p: LKProof ): LKProof = {
    val edmap = expand_dmap( dmap )
    eliminate_in_proof( x => BetaReduction.betaNormalize( replaceAll_in( edmap, x ) ), p )
  }

  def fixedpoint_val[A]( f: ( A => A ), l: A ): A = {
    val r = f( l )
    if ( r == l ) r else fixedpoint_val( f, r )
  }

  def fixedpoint_seq[A]( f: ( A => A ), l: Seq[A] ): Seq[A] = {
    val r = l map f
    if ( r == l ) r else fixedpoint_seq( f, r )
  }

  /**
   * Converts a function of type LambdaExpression => LambdaExpression to type HOLFormula => HOLFormula.
   *
   * @param f
   * @return
   */
  private def hol( f: LambdaExpression => LambdaExpression ): HOLFormula => HOLFormula = e => f( e ).asInstanceOf[HOLFormula]

  def replaceAll_informula( dmap: DefinitionsMap, e: HOLFormula ): HOLFormula = replaceAll_in( dmap, e ).asInstanceOf[HOLFormula]

  def replaceAll_in( dmap: DefinitionsMap, e: LambdaExpression ): LambdaExpression = {
    e match {
      case Const( _, _ ) => try_to_match( dmap, e )
      case Var( _, _ )   => try_to_match( dmap, e )
      case Neg( s )      => Neg( replaceAll_informula( dmap, s ) )
      case And( s, t )   => And( replaceAll_informula( dmap, s ), replaceAll_informula( dmap, t ) )
      case Or( s, t )    => Or( replaceAll_informula( dmap, s ), replaceAll_informula( dmap, t ) )
      case Imp( s, t )   => Imp( replaceAll_informula( dmap, s ), replaceAll_informula( dmap, t ) )
      case All( x, t )   => All( x, replaceAll_informula( dmap, t ) )
      case Ex( x, t )    => Ex( x, replaceAll_informula( dmap, t ) )
      case App( s, t ) =>
        val fullmatch = try_to_match( dmap, e )
        if ( fullmatch == e )
          try_to_match( dmap, App( replaceAll_in( dmap, s ), replaceAll_in( dmap, t ) ).asInstanceOf[LambdaExpression] )
        else
          replaceAll_in( dmap, fullmatch )
      case Abs( x, t ) => Abs( x, replaceAll_in( dmap, t ) ).asInstanceOf[LambdaExpression]
    }
  }

  def try_to_matchformula( dmap: DefinitionsMap, e: LambdaExpression ) = try_to_match( dmap, e ).asInstanceOf[HOLFormula]

  def try_to_match( dmap: DefinitionsMap, e: LambdaExpression ): LambdaExpression = {
    dmap.keys.foldLeft( e )( ( v, key ) => {
      //      println("matching " + v + " against " + key)
      NaiveIncompleteMatchingAlgorithm.matchTerm( key, v, Set() ) match {
        case None => v
        case Some( sub ) =>
          val r = sub( dmap( key ) )
          //          println("YES! "+sub)
          r
      }
    } )
  }

  def expand_dmap( dmap: DefinitionsMap ): DefinitionsMap = {
    val ndmap = dmap map ( x => {
      ( x._1, replaceAll_in( dmap, x._2 ) )
    } )

    if ( ndmap == dmap )
      dmap
    else expand_dmap( ndmap )
  }

  private def eliminate_from_( defs: ProcessedDefinitionsMap, f: HOLFormula ): HOLFormula = {
    f match {
      case Neg( f1 )     => Neg( eliminate_from_( defs, f1 ) )
      case All( q, f1 )  => All( q, eliminate_from_( defs, f1 ) )
      case Ex( q, f1 )   => Ex( q, eliminate_from_( defs, f1 ) )
      case And( f1, f2 ) => And( eliminate_from_( defs, f1 ), eliminate_from_( defs, f2 ) )
      case Imp( f1, f2 ) => Imp( eliminate_from_( defs, f1 ), eliminate_from_( defs, f2 ) )
      case Or( f1, f2 )  => Or( eliminate_from_( defs, f1 ), eliminate_from_( defs, f2 ) )
      case HOLAtom( e, args ) =>
        val sym = e match {
          case v: Var   => v.sym
          case c: Const => c.sym
        }

        defs.get( sym ) match {
          case Some( ( definition_args, defined_formula ) ) =>
            if ( args.length != definition_args.length ) {
              println( "Warning: ignoring definition replacement because argument numbers dont match!" )
              f
            } else {
              //we need to insert the correct values for the free variables in the definition
              //the casting is needed since we cannot make a map covariant
              //val pairs = (definition_args zip args)  filter ((x:(LambdaExpression, LambdaExpression) ) => x._1.isInstanceOf[Var])
              val pairs = definition_args zip args
              val sub = Substitution( pairs )
              println( "Substitution:" )
              println( sub )
              sub.apply( defined_formula ).asInstanceOf[HOLFormula]
            }
          case _ => f
        }
      case _ => println( "Warning: unhandled case in definition elimination!" ); f
    }
  }

  private val emptymap = Map[SequentIndex, SequentIndex]() //this will be passed to some functions

  def eliminate_in_proof( rewrite: ( LambdaExpression => LambdaExpression ), proof: LKProof ): LKProof =
    eliminate_in_proof_( rewrite, proof )

  /**
   * Applies a function of type LambdaExpression => LambdaExpression to an LKProof.
   *
   * The only case where anything really happens is with definition rules.
   *
   * @param rewrite A function of type LambdaExpression => LambdaExpression.
   * @param proof An LKProof.
   * @return The result of applying rewrite everywhere in proof.
   */
  def eliminate_in_proof_( rewrite: ( LambdaExpression => LambdaExpression ), proof: LKProof ): LKProof = {
    def recCall( proof: LKProof ) = eliminate_in_proof_( rewrite, proof )

    proof match {
      // introductory rules
      case LogicalAxiom( atom ) =>
        AtomicExpansion( hol( rewrite )( atom ) )

      case InitialSequent( sequent ) =>
        debug( "Axiom!" )
        val sequentNew = sequent.map( f => hol( rewrite )( f ) )
        val proofNew = Axiom( sequentNew )

        proofNew

      //structural rules
      case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        debug( "Cut!" )
        val leftSubProofNew = recCall( leftSubProof )
        val rightSubProofNew = recCall( rightSubProof )
        debug( "aux:  " + aux1 + " and " + aux2 )

        val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
        proofNew

      case WeakeningLeftRule( subProof, main ) =>
        debug( "Weakening Left!" )
        val subProofNew = recCall( subProof )
        val proofNew = WeakeningLeftRule( subProofNew, hol( rewrite )( main ) )

        proofNew

      case WeakeningRightRule( subProof, main ) =>
        debug( "Weakening Right!" )
        val subProofNew = eliminate_in_proof_( rewrite, subProof )
        val proofNew = WeakeningRightRule( subProofNew, hol( rewrite )( main ) )

        proofNew

      case ContractionLeftRule( subProof, aux1, aux2 ) =>
        debug( "Contraction Left!" )
        val subProofNew = recCall( subProof )

        ContractionLeftRule( subProofNew, aux1, aux2 )

      case ContractionRightRule( subProof, aux1, aux2 ) =>
        debug( "Contraction Right!" )
        val subProofNew = recCall( subProof )

        ContractionRightRule( subProofNew, aux1, aux2 )

      //logical rules
      case NegLeftRule( subProof, aux ) =>
        debug( "Negation Left!" )
        val subProofNew = recCall( subProof )

        NegLeftRule( subProofNew, aux )

      case NegRightRule( subProof, aux ) =>
        debug( "Negation Right!" )
        val subProofNew = recCall( subProof )

        NegRightRule( subProofNew, aux )

      case AndLeftRule( subProof, aux1, aux2 ) =>
        debug( "And Left!" )
        val subProofNew = recCall( subProof )

        AndLeftRule( subProofNew, aux1, aux2 )

      case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        debug( "And Right!" )
        val leftSubProofNew = recCall( leftSubProof )
        val rightSubProofNew = recCall( rightSubProof )
        debug( "aux:  " + aux1 + " and " + aux2 )

        val proofNew = AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
        proofNew

      case OrRightRule( subProof, aux1, aux2 ) =>
        debug( "Or Right!" )
        val subProofNew = recCall( subProof )

        OrRightRule( subProofNew, aux1, aux2 )

      case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        debug( "Or Left!" )
        val leftSubProofNew = recCall( leftSubProof )
        val rightSubProofNew = recCall( rightSubProof )
        debug( "aux:  " + aux1 + " and " + aux2 )

        val proofNew = OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
        proofNew

      case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
        debug( "Imp Left!" )
        val leftSubProofNew = recCall( leftSubProof )
        val rightSubProofNew = recCall( rightSubProof )
        debug( "aux:  " + aux1 + " and " + aux2 )

        val proofNew = ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )
        proofNew

      case ImpRightRule( subProof, aux1, aux2 ) =>
        debug( "Imp Right!" )
        val subProofNew = recCall( subProof )

        ImpRightRule( subProofNew, aux1, aux2 )

      //quantfication rules
      case ForallLeftRule( subProof, aux, f, term, quant ) =>
        debug( "Forall Left" )
        val subProofNew = recCall( subProof )

        ForallLeftRule( subProofNew, aux, hol( rewrite )( f ), rewrite( term ), rewrite( quant ).asInstanceOf[Var] )

      case ForallRightRule( subProof, aux, eigen, quant ) =>
        debug( "Forall Right!" )
        val subProofNew = recCall( subProof )

        ForallRightRule( subProofNew, aux, eigen, rewrite( quant ).asInstanceOf[Var] )

      case ExistsLeftRule( subProof, aux, eigen, quant ) =>
        debug( "Exists Left!" )
        val subProofNew = recCall( subProof )

        ExistsLeftRule( subProofNew, aux, eigen, rewrite( quant ).asInstanceOf[Var] )

      case ExistsRightRule( subProof, aux, f, term, quant ) =>
        debug( "Exists Right!" )
        val subProofNew = recCall( subProof )

        ExistsRightRule( subProofNew, aux, hol( rewrite )( f ), rewrite( term ), rewrite( quant ).asInstanceOf[Var] )

      //equational rules
      case EqualityLeftRule( subProof, eq, aux, pos ) =>
        debug( "Equation Left!" )
        val subProofNew = recCall( subProof )
        val mainNew = hol( rewrite )( proof.mainFormulas.head )

        EqualityLeftRule( subProofNew, eq, aux, mainNew )

      case EqualityRightRule( subProof, eq, aux, pos ) =>
        debug( "Equation Right!" )
        val subProofNew = recCall( subProof )
        val mainNew = hol( rewrite )( proof.mainFormulas.head )

        EqualityRightRule( subProofNew, eq, aux, mainNew )

      /* The cases for definition rules employ a trick: The removal of the rule would change the order of the end
        sequent. We use exchange macro rules to artificially replicate the movement of formulas that the definition
         rule would have performed.*/

      case DefinitionLeftRule( subProof, aux, main ) =>
        debug( "Def Left!" )
        val subProofNew = recCall( subProof )

        ExchangeLeftMacroRule( subProofNew, aux )

      case DefinitionRightRule( subProof, aux, main ) =>
        debug( "Def Right!" )
        val subProofNew = recCall( subProof )

        ExchangeRightMacroRule( subProofNew, aux )

    }

  }
}