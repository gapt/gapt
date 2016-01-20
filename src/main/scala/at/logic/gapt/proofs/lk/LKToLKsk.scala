package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.TypeSynonyms.SkolemSymbol
import at.logic.gapt.expr.hol.{ HOLPosition, SkolemSymbolFactory }
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lkskNew.LKskProof._
import at.logic.gapt.proofs.lkskNew
import at.logic.gapt.proofs.lk
import at.logic.gapt.proofs.lkskNew._
import at.logic.gapt.utils.logging.Logger

class LKToLKsk( skolemSymbolFactory: SkolemSymbolFactory ) extends Logger {
  type HPathsSequent = Sequent[List[HPath]]
  type SkolemSymbolTable = Map[HPath, SkolemSymbol]

  def apply( p: LKProof ): LKskProof = apply( p, p.conclusion map { _ => Seq() },
    p.conclusion map { _ => false },
    p.conclusion map { _ => Nil } )( Map() )._1

  def apply( p: LKProof, labels: Sequent[Label], isCutAnc: Sequent[Boolean], hpaths: HPathsSequent )( implicit contracted_symbols: SkolemSymbolTable ): ( LKskProof, SkolemSymbolTable ) = {
    val res: ( LKskProof, SkolemSymbolTable ) = p match {
      case LogicalAxiom( atom )     => ( lkskNew.Axiom( labels( Ant( 0 ) ), labels( Suc( 0 ) ), atom ), contracted_symbols )
      case ReflexivityAxiom( term ) => ( Reflexivity( labels( Suc( 0 ) ), term ), contracted_symbols )
      case TopAxiom                 => ( TopRight( labels( Suc( 0 ) ) ), contracted_symbols )
      case BottomAxiom              => ( BottomLeft( labels( Ant( 0 ) ) ), contracted_symbols )
      case lk.TheoryAxiom( seq )    => ( lkskNew.TheoryAxiom( labels zip seq ), contracted_symbols )

      case p @ ContractionLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        val nhpath = extend_hpaths( p, hpaths.zipWithIndex map ( {
          case ( path, i ) if i == aux1 =>
            HPath( p, List( p.mainFormula ) ) :: path
          case ( path, i ) if i == aux2 =>
            HPath( p, List( p.mainFormula ) ) :: path
          case ( path, _ ) =>
            path
        } ) )
        val ( uproof, utable ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), nhpath )
        ( ContractionLeft( uproof, aux1, aux2 ), utable )
      case p @ ContractionRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        val nhpath = extend_hpaths( p, hpaths.zipWithIndex map ( {
          case x if x._2 == aux1 || x._2 == aux2 => HPath( p, List( p.mainFormula ) ) :: x._1
          case x                                 => x._1
        } ) )
        val ( uproof, utable ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), nhpath )
        ( ContractionRight( uproof, aux1, aux2 ), utable )

      case p @ WeakeningLeftRule( subProof, formula ) =>
        val ( uproof, utable ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( WeakeningLeft( uproof, labels( p.mainIndices.head ) -> formula ), utable )
      case p @ WeakeningRightRule( subProof, formula ) =>
        val ( uproof, utable ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( WeakeningRight( uproof, labels( p.mainIndices.head ) -> formula ), utable )

      case p @ NegLeftRule( subProof, aux: Suc ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( NegLeft( uproof, aux ), table )
      case p @ NegRightRule( subProof, aux: Ant ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( NegRight( uproof, aux ), table )

      case p @ AndLeftRule( subProof, aux1: Ant, aux2: Ant ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( AndLeft( uproof, aux1, aux2 ), table )
      case p @ AndRightRule( subProof1, aux1: Suc, subProof2, aux2: Suc ) =>
        val ( uproof1, table1 ) = apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 0 ) )
        val ( uproof2, table2 ) = apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 1 ) )( table1 )
        ( AndRight( uproof1, aux1, uproof2, aux2 ), table2 )

      case p @ OrLeftRule( subProof1, aux1: Ant, subProof2, aux2: Ant ) =>
        val ( uproof1, table1 ) = apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 0 ) )
        val ( uproof2, table2 ) = apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 1 ) )( table1 )
        ( OrLeft( uproof1, aux1, uproof2, aux2 ), table2 )
      case p @ OrRightRule( subProof, aux1: Suc, aux2: Suc ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( OrRight( uproof, aux1, aux2 ), table )

      case p @ ImpLeftRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        val ( uproof1, table1 ) = apply( subProof1, p.getLeftOccConnector.parent( labels ), p.getLeftOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 0 ) )
        val ( uproof2, table2 ) = apply( subProof2, p.getRightOccConnector.parent( labels ), p.getRightOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths, 1 ) )( table1 )
        ( ImpLeft( uproof1, aux1, uproof2, aux2 ), table2 )
      case p @ ImpRightRule( subProof, aux1: Ant, aux2: Suc ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( ImpRight( uproof, aux1, aux2 ), table )

      case p @ CutRule( subProof1, aux1: Suc, subProof2, aux2: Ant ) =>
        val ( uproof1, table1 ) = apply( subProof1, p.getLeftOccConnector.parent( labels, Seq() ), p.getLeftOccConnector.parent( isCutAnc, true ), extend_hpaths( p, hpaths, 0 ) )
        val ( uproof2, table2 ) = apply( subProof2, p.getRightOccConnector.parent( labels, Seq() ), p.getRightOccConnector.parent( isCutAnc, true ), extend_hpaths( p, hpaths, 1 ) )( table1 )
        ( Cut( uproof1, aux1, uproof2, aux2 ), table2 )

      case p: EqualityRule =>
        val lambdaPos = p.positions map { HOLPosition.toLambdaPosition( p.auxFormula ) }
        val ( uproof, table ) = apply( p.subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( Equality( uproof, p.eq.asInstanceOf[Ant], p.aux, p.leftToRight, lambdaPos ), table )

      case p @ ForallLeftRule( subProof, aux: Ant, formula, term, v ) if !isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( AllSkLeft( uproof, aux, All( v, formula ), term ), table )
      case p @ ExistsRightRule( subProof, aux: Suc, formula, term, v ) if !isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ).updated( aux, labels( p.mainIndices.head ) :+ term ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( ExSkRight( uproof, aux, Ex( v, formula ), term ), table )
      case p @ ForallLeftRule( subProof, aux: Ant, formula, term, v ) if isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( AllLeft( uproof, aux, All( v, formula ), term ), table )
      case p @ ExistsRightRule( subProof, aux: Suc, formula, term, v ) if isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( ExRight( uproof, aux, Ex( v, formula ), term ), table )

      case p @ ForallRightRule( subProof, aux: Suc, eigen, quant ) if !isCutAnc( p.mainIndices.head ) =>
        val ls = labels( p.mainIndices.head )
        val ( skolemSymbol, newTable ) = createSkolemSymbol( skolemSymbolFactory, hpaths( p.mainIndices( 0 ) ), contracted_symbols )
        val skolemConstant = Const( skolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = Substitution( eigen -> skolemConstant( ls: _* ) )( subProof )
        val ( uproof, table ) = apply( subProof_, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )( newTable )
        ( AllSkRight( uproof, aux, p.mainFormula, skolemConstant ), table )

      case p @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) if !isCutAnc( p.mainIndices.head ) =>
        val ls = labels( p.mainIndices.head )
        val ( skolemSymbol, newTable ) = createSkolemSymbol( skolemSymbolFactory, hpaths( p.mainIndices( 0 ) ), contracted_symbols )
        val skolemConstant = Const( skolemSymbol, FunctionType( eigen.exptype, ls.map( _.exptype ) ) )
        val subProof_ = Substitution( eigen -> skolemConstant( ls: _* ) )( subProof )
        val ( uproof, table ) = apply( subProof_, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )( newTable )
        ( ExSkLeft( uproof, aux, p.mainFormula, skolemConstant ), table )

      case p @ ForallRightRule( subProof, aux: Suc, eigen, quant ) if isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( AllRight( uproof, aux, p.mainFormula, eigen ), table )
      case p @ ExistsLeftRule( subProof, aux: Ant, eigen, quant ) if isCutAnc( p.mainIndices.head ) =>
        val ( uproof, table ) = apply( subProof, p.getOccConnector.parent( labels ), p.getOccConnector.parent( isCutAnc ), extend_hpaths( p, hpaths ) )
        ( ExLeft( uproof, aux, p.mainFormula, eigen ), table )
    }
    require( res._1.labels == labels, s"${res._1.labels} == $labels" )
    res
  }

  def createSkolemSymbol( factory: SkolemSymbolFactory, current_hpaths: List[HPath], symbol_table: SkolemSymbolTable ): ( SkolemSymbol, SkolemSymbolTable ) = {
    //println( s"creating skolem symbol for $current_hpaths" )
    //println( s"symbol table is:" )
    //symbol_table.map( x => println( s"${x._1} -> ${x._2}" ) )
    //we reverse the list to have the longest hpath first. since find returns the first match, it will find the longest matching hpath.
    current_hpaths.reverse.find( symbol_table.contains ) match {
      case Some( hpath ) =>
        debug( "reusing skolem symbol: " + symbol_table( hpath ) )
        ( symbol_table( hpath ), symbol_table )
      case None =>
        val sym = factory.getSkolemSymbol
        debug( s"new skolem symbol $sym" )
        val ntable = current_hpaths.foldLeft( symbol_table )( ( t, path ) => t + ( ( path, sym ) ) )
        ( sym, ntable )
    }
  }

  def extend_hpaths( p: LKProof, hpaths: HPathsSequent, occ_conn_idx: Int = 0, default: List[HPath] = Nil ): HPathsSequent = {
    //map conclusion index to ancestor indices in parent
    val anc_indices = hpaths.zipWithIndex.map( x => ( x._1, p.occConnectors( occ_conn_idx ).parents( x._2 ) ) )
    //iterate parent indices and check if it occurs in one of the ancestor indices, if not use default
    val nhpsequent = p.immediateSubProofs( occ_conn_idx ).conclusion.zipWithIndex.map( x => {
      anc_indices find ( _._2 contains x._2 ) match {
        case Some( idx ) =>
          val oldpaths = anc_indices( idx )._1
          //add new formula
          //println( "extending: " + x._1 )
          oldpaths map ( _ extend x._1 )
        case None => default
      }
    } )
    nhpsequent
  }

  case class HPath( contracting_inference: LKProof, path: List[HOLFormula] ) {
    /** extends a homomorphic path by formula f. since homomorphic paths don't have repetitions, skip them. */
    def extend( f: HOLFormula ): HPath = path match {
      case x :: xs if x == f => HPath( contracting_inference, path )
      case _                 => HPath( contracting_inference, f :: path )
    }

    def extend( p: LKProof ): HPath = extend( p.mainFormulas( 0 ) )
    override def toString() = s"HPath(${contracting_inference.hashCode}, $path)"
  }
}

object LKToLKsk {
  def apply( p: LKProof ): LKskProof = ( new LKToLKsk( new SkolemSymbolFactory ) )( p )
}

/**
 * \Gamma :- P(s(q)), \Delta                               \Gamma :- P(s(q)), \Delta
 * --------------------------------- all:l                 --------------------------------- all:l
 * \Gamma :- \forall x P(x), \Delta                        \Gamma :- \forall x P(x), \Delta
 * ----------------------------------------------------------------------------------------- X:l
 *      \Gamma' :- \forall x P(x), \forall x P(x), \Delta
 *      ------------------------------------------------- c:r
 *      \Gamma' :- \forall x P(x), \Delta
 */
