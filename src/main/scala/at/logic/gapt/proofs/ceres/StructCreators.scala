package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr._
import at.logic.gapt.utils.logging.Logger

/**
 * Algorithms extracting structs from LK proofs, preparing them for gui code etc.
 */

/**
 * Returns s.toString with color coding of struct operators. When a big struct is loaded in the cli, the string truncation
 * can mess up the terminal, therefore this is not the default behaviour.
 */
object coloredStructString {
  def apply[Data]( s: Struct[Data] ) = s match {
    case A( fo, _ ) =>
      fo.toString
    case Dual( sub ) =>
      Console.GREEN + "~(" + Console.RESET + sub + Console.GREEN + ")" + Console.RESET
    case Times( left, right, _ ) =>
      Console.RED + "(" + Console.RESET + left + Console.RED + " ⊗ " + Console.RESET + right + Console.RED + ")" + Console.RESET
    case Plus( left, right ) =>
      Console.BLUE + "(" + Console.RESET + left + Console.BLUE + " ⊕ " + Console.RESET + right + Console.BLUE + ")" + Console.RESET
    case EmptyPlusJunction()  => Console.RED + "ε" + Console.RESET
    case EmptyTimesJunction() => Console.BLUE + "ε" + Console.RESET
  }
}

object StructCreators extends Logger {
  def size[Data]( s: Struct[Data] ): Int = size( s, 0 )
  //TODO:make tailrecursive
  def size[Data]( s: Struct[Data], n: Int ): Int = s match {
    case A( _, _ )            => n
    case Dual( x )            => size( x, n + 1 )
    case Plus( l, r )         => size( l, size( r, n + 1 ) )
    case Times( l, r, _ )     => size( l, size( r, n + 1 ) )
    case EmptyPlusJunction()  => n
    case EmptyTimesJunction() => n
  }

  val nLine = sys.props( "line.separator" )

  def toFormula[Data]( s: Struct[Data] ): HOLFormula =
    And( CharacteristicClauseSet( s ).toSeq map ( _.toFormula ) )

  def extract[Data]( p: LKProof ): Struct[Data] =
    extract[Data]( p, p.endSequent.map( _ => false ) )( x => true )
  def extract[Data]( p: LKProof, predicate: HOLFormula => Boolean ): Struct[Data] =
    extract[Data]( p, p.endSequent.map( _ => false ) )( predicate )

  private def mapToUpperProof[Formula]( conn: OccConnector[Formula], cut_occs: Sequent[Boolean], default: Boolean ) =
    conn.parents( cut_occs ).map( _.headOption getOrElse default )

  def extract[Data]( p: LKProof, cut_occs: Sequent[Boolean] )( implicit pred: HOLFormula => Boolean ): Struct[Data] = {
    val cutanc_es = p.endSequent.zip( cut_occs ).filter( _._2 ).map( _._1 )
    val es = p.endSequent
    /*println( s"es: $es" )
    println( s"ca: $cutanc_es" )
    println()*/
    p match {
      case ReflexivityAxiom( e ) =>
        if ( cut_occs( Suc( 0 ) ) )
          A( Eq( e, e ) )
        else
          EmptyTimesJunction()
      case InitialSequent( so ) =>
        handleAxiom( so, cut_occs )

      case EqualityLeftRule( upperProof, eq, aux, pos ) =>
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        val struct = extract[Data]( upperProof, new_occs )
        val e_idx_conclusion = p.occConnectors( 0 ).child( eq )
        //println( "eql: " + p.endSequent( eq ) )
        ( cut_occs( p.mainIndices( 0 ) ), cut_occs( e_idx_conclusion ) ) match {
          case ( true, true ) =>
            struct
          case ( true, false ) =>
            Plus( A( p.mainFormulas( 0 ), Nil ), struct )
          case ( false, true ) =>
            Times( Dual( A( p.endSequent( eq ), Nil ) ), struct, Nil )
          case ( false, false ) =>
            struct
        }

      case EqualityRightRule( upperProof, eq, aux, pos ) =>
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        val struct = extract[Data]( upperProof, new_occs )
        val e_idx_conclusion = p.occConnectors( 0 ).child( eq )
        //println( "eqr: " + p.endSequent( eq ) )
        ( cut_occs( p.mainIndices( 0 ) ), cut_occs( e_idx_conclusion ) ) match {
          case ( true, true ) =>
            struct
          case ( true, false ) =>
            Plus( A( p.endSequent( e_idx_conclusion ), Nil ), struct )
          case ( false, true ) =>
            Times( Dual( A( p.endSequent( e_idx_conclusion ), Nil ) ), struct, Nil )
          case ( false, false ) =>
            struct
        }

      case UnaryLKProof( _, upperProof ) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula!"
        )
        val new_occs = p.occConnectors( 0 ).parents( cut_occs ).flatMap { case Seq() => Seq(); case x => Seq( x.head ) }
        extract[Data]( upperProof, new_occs )

      case rule @ CutRule( p1, aux1, p2, aux2 ) =>
        if ( pred( rule.cutFormula ) ) {
          val new_occs1 = mapToUpperProof( p.occConnectors( 0 ), cut_occs, true )
          val new_occs2 = mapToUpperProof( p.occConnectors( 1 ), cut_occs, true )
          Plus[Data](
            extract[Data]( p1, new_occs1 ),
            extract[Data]( p2, new_occs2 )
          )
        } else {
          val new_occs1 = mapToUpperProof( p.occConnectors( 0 ), cut_occs, false )
          val new_occs2 = mapToUpperProof( p.occConnectors( 1 ), cut_occs, false )
          Times[Data](
            extract[Data]( p1, new_occs1 ),
            extract[Data]( p2, new_occs2 ), List()
          )
        }

      case BinaryLKProof( _, upperProofLeft, upperProofRight ) =>
        require(
          p.mainIndices.size == 1,
          "Error: Struct extraction only works for rules which have exactly one primary formula! " + p
        )
        val new_occs1 = p.occConnectors( 0 ).parents( cut_occs ).map( _.head )
        val new_occs2 = p.occConnectors( 1 ).parents( cut_occs ).map( _.head )
        if ( cut_occs( p.mainIndices( 0 ) ) )
          Plus[Data]( extract[Data]( upperProofLeft, new_occs1 ), extract[Data]( upperProofRight, new_occs2 ) )
        else
          Times[Data]( extract[Data]( upperProofLeft, new_occs1 ), extract[Data]( upperProofRight, new_occs2 ), List() )
      case _ => throw new Exception( "Missing rule in StructCreators.extract: " + p.name )
    }
  }

  def handleAxiom[Data]( so: HOLSequent, cut_occs: Sequent[Boolean] ): Struct[Data] = {
    //printf( "Axiom!" )
    //printf( cut_occs.toString )

    val cutanc_seq: HOLSequent = so.zipWithIndex.filter( x => cut_occs( x._2 ) ).map( _._1 )
    val tautology_projection = cutanc_seq.antecedent.exists( x => cutanc_seq.succedent.contains( x ) )
    //if ( tautology_projection ) println( s"Could optimize $so ($cut_occs)" )
    //println( cutanc_seq )
    tautology_projection match {
      case true =>
        //println( "tautology " + cutanc_seq )
        /* in the case of an axiom A :- A, if both occurrences of A are cut-ancestors, we need to return plus not times.
         * treat an axiom of the form \Gamma, A :- A, \Delta as if \Gamma and \Delta were added by weakening */
        EmptyPlusJunction()
      case false =>
        val cutAncInAntecedent = cutanc_seq.antecedent.map( x => Dual[Data]( A( x, Nil ) ) )
        val cutAncInSuccedent = cutanc_seq.succedent.map( x => A[Data]( x ) )
        val structs: Seq[Struct[Data]] = cutAncInAntecedent ++ cutAncInSuccedent
        val r = Times[Data]( structs, List[Data]() )
        r
    }
  }

}

