package at.logic.gapt.proofs.ceres_omega

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.ceres.{ SimplifyStruct, Struct }
import at.logic.gapt.proofs.lkOld.subsumedClausesRemovalHOL
import at.logic.gapt.proofs.lkskNew.LKskProof.{ LabelledSequent, Label }

import scala.collection.mutable

//TODO: this is actually some glue code for interaction with first order provers -- rename and check if it is even used

object CharacteristicSequentSet {
  def apply( s: Struct[Label] ): ( List[LabelledSequent], List[HOLSequent], List[HOLSequent], FOLConstantsMap ) = {
    val clauselist = StandardClauseSet( SimplifyStruct( s ) )
    val ( fcmap, fol, hol ) = apply( clauselist.toList )
    ( clauselist.toList, fol, hol, fcmap )
  }

  def apply( l: List[LabelledSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) =
    prunes( l )

  def prunes( l: List[LabelledSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) = {
    prunefs( l map ( _.map( _._2 ) ) )
  }

  def prunefs( l: List[HOLSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) = {
    val ( fcmap, fol ) = extractFOL( l )
    ( fcmap, subsumedClausesRemovalHOL( fol ), extractHOL( l ).toSet.toList )
  }

  type FOLConstantsMap = Map[String, FOLExpression]

  def extractFOL( l: List[HOLSequent] ): ( FOLConstantsMap, List[HOLSequent] ) = {
    val map = mutable.Map[FOLExpression, String]()
    val counter = new {
      private var state = 0;

      def nextId = {
        state = state + 1; state
      }
    }

    val fol = l.flatMap( x => try {
      x :: Nil
    } catch {
      case e: Exception => Nil
    } )

    val rmap = map.foldLeft( Map[String, FOLExpression]() )( ( m, pair ) => {
      require( !m.isDefinedAt( pair._2 ), "No duplicate constant assignment allowed during reduceHolToFol conversion!" )
      m + ( ( pair._2, pair._1 ) )
    } )
    ( rmap, fol )
  }

  def extractHOL( l: List[HOLSequent] ): List[HOLSequent] = l.flatMap( x => try {
    x.toFormula
    Nil
  } catch {
    case e: Exception => x :: Nil
  } )

  type Symboltable = ( Map[Ty, Set[String]], Map[Ty, Set[String]] )
  val emptysmboltable = ( Map[Ty, Set[String]](), Map[Ty, Set[String]]() )

  def extractSymbolTable( l: List[HOLSequent] ): Symboltable =
    l.foldLeft( emptysmboltable )( ( table, x ) => {
      val ( vt, ct ) = extractSymbolTable( x.toFormula )
      val ( vt_, ct_ ) = table
      ( vt ++ vt_, ct ++ ct_ )
    } )

  def extractSymbolTable( l: LambdaExpression ): Symboltable = l match {
    case Var( sym, ta ) =>
      val ( vt, ct ) = emptysmboltable
      ( vt + ( ( ta, Set( sym ) ) ), ct )
    case NonLogicalConstant( sym, ta ) =>
      val ( vt, ct ) = emptysmboltable
      ( vt, ct + ( ( ta, Set( sym ) ) ) )
    case App( s, t ) =>
      val ( vt1, ct1 ) = extractSymbolTable( s )
      val ( vt2, ct2 ) = extractSymbolTable( t )
      ( vt1 ++ vt2, ct1 ++ ct2 )
    case Abs( x, t ) =>
      val ( vt1, ct1 ) = extractSymbolTable( x )
      val ( vt2, ct2 ) = extractSymbolTable( t )
      ( vt1 ++ vt2, ct1 ++ ct2 )
    case _ => emptysmboltable
  }
}
