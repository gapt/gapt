package gapt.provers.sat

import gapt.formats.dimacs.DIMACS
import gapt.formats.dimacs.DIMACS.{ CNF, DRUP }
import org.sat4j.core.{ LiteralsUtils, Vec, VecInt }
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs._
import org.sat4j.tools.SearchListenerAdapter

class Sat4j extends DrupSolver {
  import Sat4j._

  override def solve( cnf: DIMACS.CNF ): Option[DIMACS.Model] = {
    val solver = SolverFactory.newDefault()
    solver.newVar( DIMACS maxAtom cnf )

    try {
      solver.addAllClauses( cnf )

      if ( solver.isSatisfiable ) {
        Some( solver.model() )
      } else {
        None
      }
    } catch {
      case _: ContradictionException => None
    }
  }

  class RupListener extends SearchListenerAdapter[ISolverService] {
    val drup = Seq.newBuilder[DIMACS.DrupInference]

    override def learnUnit( p: Int ) = drup += DIMACS.DrupDerive( Seq( p ) )
    override def learn( c: IConstr ) = drup += DIMACS.DrupDerive( c )

    override def end( result: Lbool ) =
      if ( result == Lbool.FALSE ) drup += DIMACS.DrupDerive( Seq() )
  }

  override def getDrupProof( cnf: CNF ): Option[DRUP] = {
    val solver = SolverFactory.newDefault()
    val listener = new RupListener
    solver.setSearchListener( listener )
    solver.newVar( DIMACS maxAtom cnf )

    try {
      solver.addAllClauses( cnf )

      if ( solver.isSatisfiable ) {
        None
      } else {
        Some( listener.drup.result() )
      }
    } catch {
      case _: ContradictionException =>
        listener.end( Lbool.FALSE )
        Some( listener.drup.result() )
    }
  }
}

object Sat4j extends Sat4j {
  implicit def clause2sat4j( clause: DIMACS.Clause ): IVecInt =
    new VecInt( clause toArray )

  implicit def cnf2sat4j( cnf: DIMACS.CNF ): IVec[IVecInt] =
    new Vec( cnf.map { implicitly[IVecInt]( _ ) }.toArray )

  implicit def sat4j2clause( constr: IConstr ): DIMACS.Clause =
    for ( i <- 0 until constr.size() ) yield LiteralsUtils.toDimacs( constr get i )
}
