package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.{ HOLAtom, LambdaPosition, Eq }
import at.logic.gapt.proofs.{ HOLClause, FOLClause }

object forgetfulPropResolve {
  def apply( cnf: Set[HOLClause] ): Set[Set[HOLClause]] =
    for (
      clause1 <- cnf; clause2 <- cnf; if clause1 != clause2;
      atom1 <- clause1.succedent; atom2 <- clause2.antecedent; if atom1 == atom2
    ) yield cnf - clause1 - clause2 + ( clause1.removeFromSuccedent( atom1 ) ++ clause2.removeFromAntecedent( atom2 ) ).distinct.sortBy { _.hashCode }

  def apply( cnf: Set[FOLClause] )( implicit dummyImplicit: DummyImplicit ): Set[Set[FOLClause]] =
    apply( cnf.asInstanceOf[Set[HOLClause]] ).asInstanceOf[Set[Set[FOLClause]]]
}

object forgetfulPropParam {
  def apply( cnf: Set[HOLClause] ): Set[Set[HOLClause]] =
    for (
      clause1 <- cnf; clause2 <- cnf; if clause1 != clause2;
      atom1 @ Eq( s, t ) <- clause1.succedent; ( atom2, atom2Idx ) <- clause2.zipWithIndex.elements;
      pos2 <- LambdaPosition.getPositions( atom2 ) if atom2( pos2 ) == s || atom2( pos2 ) == t
    ) yield cnf - clause1 - clause2 + ( clause1.removeFromSuccedent( atom1 ) ++ clause2.updated(
      atom2Idx,
      atom2.replace( pos2, if ( atom2( pos2 ) == s ) t else s ).asInstanceOf[HOLAtom]
    ) ).distinct.sortBy { _.hashCode }

  def apply( cnf: Set[FOLClause] )( implicit dummyImplicit: DummyImplicit ): Set[Set[FOLClause]] =
    apply( cnf.asInstanceOf[Set[HOLClause]] ).asInstanceOf[Set[Set[FOLClause]]]
}
