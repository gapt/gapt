package at.logic.gapt.provers.sat

import at.logic.gapt.examples.PigeonHolePrinciple
import at.logic.gapt.expr._
import at.logic.gapt.models.Interpretation
import at.logic.gapt.proofs.{ HOLSequent, HOLClause }

object SATProblems {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val e = FOLConst( "e" )
  val pc = FOLAtom( "P", c :: Nil )
  val pd = FOLAtom( "P", d :: Nil )
  val pe = FOLAtom( "P", e :: Nil )

  def getProblem1() = HOLClause( Nil, pc :: Nil ) :: Nil
  def getProblem2() = {
    val c1 = HOLClause( Nil, pc :: Nil )
    val c2 = HOLClause( pc :: Nil, Nil )
    c1 :: c2 :: Nil
  }
  def getProblem3a() = Or( pc, Neg( pc ) )
  def getProblem3b() = new HOLSequent( Nil, Or( pc, Neg( pc ) ) :: Nil )
  def getProblem4() = pc
  def getProblem5() = {
    val c1 = HOLClause( Nil, pc :: Nil )
    val c2 = HOLClause( pc :: Nil, pd :: Nil )
    val c3 = HOLClause( pd :: pe :: Nil, Nil )
    c1 :: c2 :: c3 :: Nil
  }
  def checkSolution5( model: Interpretation ) = model.interpret( pe ) == false

  private def problem6( pair: ( Int, Int ) ) = PigeonHolePrinciple( pair._1, pair._2 )

  def getProblem6a(): List[FOLFormula] = {
    val fparams = List( ( 2, 2 ), ( 3, 3 ), ( 4, 4 ) )
    fparams.map( problem6 )
  }

  def getProblem6b(): List[FOLFormula] = {
    val tparams = List( ( 2, 1 ), ( 3, 2 ), ( 4, 3 ), ( 4, 1 ) )
    tparams.map( problem6 )
  }
}
