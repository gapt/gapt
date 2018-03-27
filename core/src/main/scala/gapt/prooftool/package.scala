package gapt

import gapt.expr.{ Formula, Expr }
import gapt.formats.latex.LatexExporter
import gapt.formats.llk.ExtendedProofDatabase
import gapt.proofs.ceres.Struct
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.lk.LKProof
import gapt.proofs.{ HOLSequent, SequentProof }
import gapt.prooftool._

import scala.annotation.implicitNotFound

private[gapt] trait ProoftoolInstances1 {
  implicit def SequentProofViewable[F, T <: SequentProof[F, T]]: ProoftoolViewable[SequentProof[F, T]] = {
    def renderer( x: F ): String = x match {
      case e: Expr => LatexExporter( e )
      case _       => x.toString
    }

    ( p, name ) => List( new SequentProofViewer( name, p, renderer ) )
  }

  implicit val ExpansionProofViewable: ProoftoolViewable[ExpansionProof] =
    ( ep, name ) => List( new ExpansionSequentViewer( name, ep.expansionSequent ) )

  implicit def StructViewable: ProoftoolViewable[Struct] =
    ( s, name ) => List( new StructViewer( name, s ) )

  implicit val ListViewable: ProoftoolViewable[Iterable[HOLSequent]] =
    ( list, name ) => List( new ListViewer( name, list.toList ) )

  implicit val SequentViewable: ProoftoolViewable[HOLSequent] =
    ( seq, name ) => List( new ListViewer( name, List( seq ) ) )

  implicit val ProofDatabaseViewable: ProoftoolViewable[ExtendedProofDatabase] =
    ( db, _ ) => db.proofs.flatMap( ( t ) => ProoftoolViewable[LKProof].display( t._2, t._1 ) )

  implicit def OptionViewable[T: ProoftoolViewable]: ProoftoolViewable[Option[T]] =
    ( oT, name ) => oT.toList.flatMap( ProoftoolViewable[T].display( _, name ) )

  implicit def EitherViewable[T: ProoftoolViewable, S]: ProoftoolViewable[Either[S, T]] =
    ( oT, name ) => oT.toOption.toList.flatMap( ProoftoolViewable[T].display( _, name ) )

}

private[gapt] trait ProoftoolInstances2 extends ProoftoolInstances1 {
  implicit val LKProofViewable: ProoftoolViewable[LKProof] =
    ( x, name ) => List( new LKProofViewer( name, x ) )
}

package object prooftool extends ProoftoolInstances2 {

  /**
   * A typeclass for things that can be displayed in Prooftool.
   * @tparam T The type of the displayed object.
   */
  @implicitNotFound( "Prooftool cannot show objects of type ${T}.\n(To support the type ${T}, add an implicit instance of ProoftoolViewable[${T}].)" )
  trait ProoftoolViewable[-T] {
    def display( x: T, name: String ): List[ProofToolViewer[_]]
  }

  object ProoftoolViewable {
    def apply[T: ProoftoolViewable] = implicitly[ProoftoolViewable[T]]
  }
}
