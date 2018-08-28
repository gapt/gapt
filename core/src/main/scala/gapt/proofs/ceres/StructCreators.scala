package gapt.proofs.ceres

import gapt.proofs._
import gapt.proofs.lk._
import gapt.expr.{ Apps, Const, _ }
import gapt.proofs.context.Context
import gapt.proofs.context.Context.{ ProofDefinitions, ProofNames }

/**
 * Algorithms extracting structs from LK proofs, preparing them for gui code etc.
 */

/**
 * Returns s.toString with color coding of struct operators. When a big struct is loaded in the cli, the string truncation
 * can mess up the terminal, therefore this is not the default behaviour.
 */
object coloredStructString {
  def apply( s: Struct ) = s match {
    case A( fo ) =>
      fo.toString
    case Dual( sub ) =>
      Console.GREEN + "~(" + Console.RESET + sub + Console.GREEN + ")" + Console.RESET
    case Times( left, right ) =>
      Console.RED + "(" + Console.RESET + left + Console.RED + " ⊗ " + Console.RESET + right + Console.RED + ")" + Console.RESET
    case Plus( left, right ) =>
      Console.BLUE + "(" + Console.RESET + left + Console.BLUE + " ⊕ " + Console.RESET + right + Console.BLUE + ")" + Console.RESET
    case EmptyPlusJunction()  => Console.RED + "ε" + Console.RESET
    case EmptyTimesJunction() => Console.BLUE + "ε" + Console.RESET
  }
}

object StructCreators {
  def size( s: Struct ): Int = size( s, 0 )
  //TODO:make tailrecursive
  def size( s: Struct, n: Int ): Int = s match {
    case A( _ )               => n
    case CLS( _, _ )          => n
    case Dual( x )            => size( x, n + 1 )
    case Plus( l, r )         => size( l, size( r, n + 1 ) )
    case Times( l, r )        => size( l, size( r, n + 1 ) )
    case EmptyPlusJunction()  => n
    case EmptyTimesJunction() => n
  }

  private val nLine = sys.props( "line.separator" )

  def toFormula( s: Struct ): Formula =
    And( CharacteristicClauseSet( s ).toSeq map ( _.toDisjunction ) )

  def extract( p: LKProof )( implicit ctx: Context ): Struct =
    extract( p, p.endSequent.map( _ => false ) )( x => true, ctx )

  def extract( p: LKProof, predicate: Formula => Boolean )( implicit ctx: Context ): Struct =
    extract( p, p.endSequent.map( _ => false ) )( predicate, ctx )

  private def mapToUpperProof[Formula]( conn: SequentConnector, cut_occs: Sequent[Boolean], default: Boolean ) =
    conn.parents( cut_occs ).map( _.headOption getOrElse default )

  def extract( p: LKProof, cut_occs: Sequent[Boolean] )( implicit pred: Formula => Boolean, ctx: Context ): Struct = {
    val cutanc_es = p.endSequent.zip( cut_occs ).filter( _._2 ).map( _._1 )
    val es = p.endSequent
    val result: Struct = p match {
      case ReflexivityAxiom( e ) =>
        if ( cut_occs( Suc( 0 ) ) )
          A( Eq( e, e ) )
        else
          EmptyTimesJunction()
      case ProofLink( rp, rs ) =>
        val Apps( Const( c, _, _ ), _ ) = rp
        if ( ctx.get[ProofDefinitions].components.keySet.contains( c ) ) handleProofLink( rs, cut_occs, rp )
        else handleAxiom( rs, cut_occs )
      case InitialSequent( so ) => handleAxiom( so, cut_occs )

      case EqualityLeftRule( upperProof, eq, aux, con ) =>
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        val struct = extract( upperProof, new_occs )
        val e_idx_conclusion = p.occConnectors( 0 ).child( eq )
        val eqformula = upperProof.endSequent( eq )
        ( cut_occs( p.mainIndices( 0 ) ), cut_occs( e_idx_conclusion ) ) match {
          case ( true, true ) =>
            struct
          case ( true, false ) =>
            Plus( A( eqformula ), struct )
          case ( false, true ) =>
            Times( Dual( A( eqformula ) ), struct )
          case ( false, false ) =>
            struct
        }

      case EqualityRightRule( upperProof, eq, aux, con ) =>
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        val struct = extract( upperProof, new_occs )
        val e_idx_conclusion = p.occConnectors( 0 ).child( eq )
        ( cut_occs( p.mainIndices( 0 ) ), cut_occs( e_idx_conclusion ) ) match {
          case ( true, true ) =>
            struct
          case ( true, false ) =>
            Plus( A( p.endSequent( e_idx_conclusion ) ), struct )
          case ( false, true ) =>
            Times( Dual( A( p.endSequent( e_idx_conclusion ) ) ), struct )
          case ( false, false ) =>
            struct
        }

      case UnaryLKProof( _, upperProof ) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula!" )
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        extract( upperProof, new_occs )

      case rule @ CutRule( p1, aux1, p2, aux2 ) =>
        if ( pred( rule.cutFormula ) ) {
          val new_occs1 = mapToUpperProof( p.occConnectors( 0 ), cut_occs, true )
          val new_occs2 = mapToUpperProof( p.occConnectors( 1 ), cut_occs, true )
          Plus(
            extract( p1, new_occs1 ),
            extract( p2, new_occs2 ) )
        } else {
          val new_occs1 = mapToUpperProof( p.occConnectors( 0 ), cut_occs, false )
          val new_occs2 = mapToUpperProof( p.occConnectors( 1 ), cut_occs, false )
          Times(
            extract( p1, new_occs1 ),
            extract( p2, new_occs2 ) )
        }

      case BinaryLKProof( _, upperProofLeft, upperProofRight ) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula! " + p )
        val new_occs1 = p.occConnectors( 0 ).parents( cut_occs ).map( _.head )
        val new_occs2 = p.occConnectors( 1 ).parents( cut_occs ).map( _.head )
        if ( cut_occs( p.mainIndices( 0 ) ) )
          Plus( extract( upperProofLeft, new_occs1 ), extract( upperProofRight, new_occs2 ) )
        else
          Times( extract( upperProofLeft, new_occs1 ), extract( upperProofRight, new_occs2 ) )
      case _ => throw new Exception( "Missing rule in StructCreators.extract: " + p.name )
    }
    result
  }

  def handleProofLink( so: HOLSequent, cut_occs: Sequent[Boolean],
                       proofLink: Expr )( implicit ctx: Context ): Struct =
    if ( Set( so.zipWithIndex.filter( x => cut_occs( x._2 ) ).map( _._1 ) ).map( y =>
      y.antecedent.exists( x => y.succedent.contains( x ) ) ).head ) EmptyPlusJunction()
    else CLS( proofLink, cut_occs )

  def handleAxiom(
    so:       HOLSequent,
    cut_occs: Sequent[Boolean] )( implicit ctx: Context ): Struct = {

    val cutanc_seq: HOLSequent = so.zipWithIndex.filter( x => cut_occs( x._2 ) ).map( _._1 )
    val tautology_projection = cutanc_seq.antecedent.exists( x => cutanc_seq.succedent.contains( x ) )
    tautology_projection match {
      case true =>
        /* in the case of an axiom A :- A, if both occurrences of A are cut-ancestors, we need to return plus not times.
         * treat an axiom of the form \Gamma, A :- A, \Delta as if \Gamma and \Delta were added by weakening */
        EmptyPlusJunction()
      case false =>
        val cutAncInAntecedent = cutanc_seq.antecedent.map( x => Dual( A( x ) ) )
        val cutAncInSuccedent = cutanc_seq.succedent.map( x => A( x ) )
        val structs: Vector[Struct] = cutAncInAntecedent ++ cutAncInSuccedent
        Times( structs )
    }
  }

}

