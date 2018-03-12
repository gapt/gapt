package gapt.examples
import gapt.expr._
import gapt.expr.hol.universalClosure
import gapt.formats.babel.BabelParser.parseFormula
import gapt.proofs.expansion.{ ExpansionProofToLK, minimalExpansionSequent }
import gapt.proofs.resolution.{ expansionProofFromInstances, structuralCNF }
import gapt.proofs.{ FOLClause, Sequent }
import gapt.prooftool.prooftool
import gapt.provers.sat.Sat4j

import scala.collection.mutable

object instprover extends Script {

  val endSequent = Stream.continually( Console.in.readLine() ).
    takeWhile( _ != null ).map( _.trim ).filter( _.nonEmpty ).
    map( parseFormula ).map( universalClosure( _ ).asInstanceOf[FOLFormula] ) ++: Sequent()

  val justifications = structuralCNF( endSequent )
  val cnf = justifications map { _.conclusion.asInstanceOf[FOLClause] }

  val done = mutable.Set[FOLClause]()
  val todo = mutable.Queue[FOLClause]( cnf.toSeq: _* )
  while ( Sat4j solve ( done ++ todo ) isDefined ) {
    val next = todo.dequeue()
    if ( !done.contains( next ) ) for {
      clause2 <- done
      clause1 = FOLSubstitution(
        rename( freeVariables( next ), freeVariables( clause2 ) ) )( next )
      ( atom1, index1 ) <- clause1.zipWithIndex.elements
      ( atom2, index2 ) <- clause2.zipWithIndex.elements
      if !index2.sameSideAs( index1 )
      mgu <- syntacticMGU( atom1, atom2 )
    } todo ++= Seq( mgu( clause1 ), mgu( clause2 ) )
    done += next
  }

  val instances = for ( clause <- cnf ) yield clause ->
    ( for {
      inst <- done ++ todo
      subst <- syntacticMatching( clause.toDisjunction, inst.toDisjunction )
    } yield subst ).toSet
  val expansionProof = expansionProofFromInstances( instances.toMap, justifications )
  val Some( minimized ) = minimalExpansionSequent( expansionProof, Sat4j )
  val lkProof = ExpansionProofToLK( minimized )

  prooftool( lkProof )

}