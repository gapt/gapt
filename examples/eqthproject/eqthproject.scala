package gapt.examples

import gapt.expr._
import gapt.expr.formula._
import gapt.expr.formula.fol._
import gapt.expr.formula.hol.instantiate
import gapt.proofs._
import gapt.provers.prover9._
import gapt.formats.lean._

object eqthproject extends Script {
   val Equation38 = fof"!x!y f(x,x)=f(x,y)"
   val Equation42 = fof"!x!y!z f(x,y)=f(x,z)"
   val goal = Sequent ( List( Equation38 ), List( Equation42 ))
   println( getLeanProof( goal ))

   /**
    * Produces Lean code to prove goal by calling prover9. Expects goal to contain two
    * universally quantified equations, one in the antecedens and one in the consequent.
    **/
   def getLeanProof( goal:HOLSequent ): String = {
     val nvars = goal( Suc( 0 )) match {
       case All.Block( xs, _ ) => xs.length
     }

     val instSuc = instantiate(goal(Suc(0)), getConstants( nvars ))
     val instGoal = goal.updated( Suc(0), instSuc )

     val p = Prover9.getLKProof( instGoal ).get

     "theorem eqimpl (G: Type*) [Magma G] (h0: " + LeanExporter.exportFormulaWithG( goal( Ant(0)) )
      + "): ( " + LeanExporter.exportFormulaWithG( goal(Suc(0))) + " ) := by\n"
      + "  intro " + getConstantNames( nvars ) + "\n"
      + LeanExporter( p )
   }

   private def getConstants( n:Int ):List[FOLTerm] = {
     var rv = List[FOLTerm]()
     for ( i <- 0 until n ) rv = rv :+ FOLConst( "a" + (i+1) ) 
     rv
   }

   private def getConstantNames( n:Int): String = {
     var rv = ""
     for (i <- 0 until n) rv += "a" + (i+1) + " "
     rv
  }
}
