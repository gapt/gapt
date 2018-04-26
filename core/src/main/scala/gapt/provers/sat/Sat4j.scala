package gapt.provers.sat

import gapt.formats.dimacs.DIMACS
import gapt.proofs.rup.RupProof
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
    val drup = Seq.newBuilder[RupProof.Line]

    override def learnUnit( p: Int ) = drup += RupProof.Rup( Set( p ) )
    override def learn( c: IConstr ) = drup += RupProof.Rup( c )

    override def end( result: Lbool ) =
      if ( result == Lbool.FALSE ) drup += RupProof.Rup( Set() )

    def result() = RupProof( drup.result() )
  }

  override def getDrupProof( cnf: DIMACS.CNF ): Option[RupProof] = {
    val solver = SolverFactory.newDefault()
    val listener = new RupListener
    listener.drup ++= cnf.view.map( RupProof.Input( _ ) )
    solver.setSearchListener( listener )
    solver.newVar( DIMACS maxAtom cnf )

    try {
      solver.addAllClauses( cnf )

      if ( solver.isSatisfiable ) {
        None
      } else {
        Some( listener.result() )
      }
    } catch {
      case _: ContradictionException =>
        listener.end( Lbool.FALSE )
        Some( listener.result() )
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
