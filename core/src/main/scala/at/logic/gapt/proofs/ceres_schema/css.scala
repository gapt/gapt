package at.logic.gapt.proofs.ceres_schema

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.ceres_schema.clauseSets.{ SimplifyStruct, StandardClauseSet }
import at.logic.gapt.proofs.ceres_schema.struct.Struct
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkOld.subsumedClausesRemoval

import scala.collection.mutable

object CharacteristicSequentSet {
  def apply( s: Struct ): ( List[HOLSequent], List[HOLSequent], List[HOLSequent], FOLConstantsMap ) = {
    val clauselist = StandardClauseSet.transformStructToClauseSet( SimplifyStruct( s ) )
    val ( fcmap, fol, hol ) = apply( clauselist )
    ( clauselist.map( _.toHOLSequent ), fol, hol, fcmap )
  }

  def apply( l: List[OccSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) =
    prunes( l )

  def prunes( l: List[OccSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) = {
    prunefs( l map ( _.toHOLSequent ) )
  }

  def prunefs( l: List[HOLSequent] ): ( FOLConstantsMap, List[HOLSequent], List[HOLSequent] ) = {
    val ( fcmap, fol ) = extractFOL( l )
    ( fcmap, subsumedClausesRemoval( fol ).sorted( HOLSequentOrdering ), extractHOL( l ).toSet.toList.sorted( HOLSequentOrdering ) )
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
