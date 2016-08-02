package at.logic.gapt

import at.logic.gapt.expr.LambdaExpression
import at.logic.gapt.formats.latex.LatexExporter
import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.{ HOLSequent, SequentProof }
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofWithCut }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.lksk.LKskProof

import scala.annotation.implicitNotFound
import scalaz.{ \/, \/- }

/**
 * Created by sebastian on 8/2/16.
 */
package object prooftool {

  @implicitNotFound( "No implementation of ProoftoolViewable found for type ${T}." )
  trait ProoftoolViewable[T] {
    def display( x: T, name: String ): Unit
  }

  implicit object LKProofViewable extends ProoftoolViewable[LKProof] {
    override def display( x: LKProof, name: String ) = new LKProofViewer( name, x ).showFrame()
  }

  implicit object LKSKProofViewable extends ProoftoolViewable[LKskProof] {
    override def display( x: LKskProof, name: String ) = new LKskProofViewer( name, x ).showFrame()
  }

  implicit def SequentProofViewable[F, T <: SequentProof[F, T]] = new ProoftoolViewable[SequentProof[F, T]] {
    override def display( p: SequentProof[F, T], name: String ) = {
      def renderer( x: F ): String = x match {
        case e: LambdaExpression => LatexExporter( e )
        case _                   => x.toString
      }
      new SequentProofViewer( name, p, renderer ).showFrame()
    }
  }

  implicit object ExpansionProofViewable extends ProoftoolViewable[ExpansionProof] {
    override def display( ep: ExpansionProof, name: String ) = new ExpansionSequentViewer( name, ep.expansionSequent ).showFrame()
  }

  implicit object ExpansionProofWithCutViewable extends ProoftoolViewable[ExpansionProofWithCut] {
    override def display( ep: ExpansionProofWithCut, name: String ) = {
      prooftool( ep.expansionWithCutAxiom, name )
    }
  }

  implicit def StructViewable[D] = new ProoftoolViewable[Struct[D]] {
    override def display( s: Struct[D], name: String ) = new StructViewer[D]( name, s ).showFrame()
  }

  implicit object ListViewable extends ProoftoolViewable[Iterable[HOLSequent]] {
    override def display( list: Iterable[HOLSequent], name: String ) = new ListViewer( name, list.toList ).showFrame()
  }

  implicit object SequentViewable extends ProoftoolViewable[HOLSequent] {
    override def display( seq: HOLSequent, name: String ) = new ListViewer( name, List( seq ) ).showFrame()
  }

  implicit object ProofDatabaseViewable extends ProoftoolViewable[ExtendedProofDatabase] {
    override def display( db: ExtendedProofDatabase, name: String ) = {
      for ( ( pName, p ) <- db.proofs )
        prooftool( p, pName )
    }
  }

  implicit def OptionViewable[T: ProoftoolViewable] = new ProoftoolViewable[Option[T]] {
    override def display( x: Option[T], name: String ) = x match {
      case Some( y ) => implicitly[ProoftoolViewable[T]].display( y, name )
      case None      => throw new IllegalArgumentException
    }
  }

  implicit def DisjViewable[T: ProoftoolViewable] = new ProoftoolViewable[\/[_, T]] {
    override def display( x: \/[_, T], name: String ) = x match {
      case \/-( y ) => implicitly[ProoftoolViewable[T]].display( y, name )
      case _        => throw new IllegalArgumentException
    }
  }
}
