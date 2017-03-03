package at.logic.gapt

import at.logic.gapt.expr.{ Formula, Expr }
import at.logic.gapt.formats.latex.LatexExporter
import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofWithCut }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ HOLSequent, SequentProof }
import at.logic.gapt.utils.Not

import scala.annotation.implicitNotFound

package object prooftool {

  /**
   * A typeclass for things that can be displayed in Prooftool.
   * @tparam T The type of the displayed object.
   */
  @implicitNotFound( "Prooftool cannot show objects of type ${T}.\n(To support the type ${T}, add an implicit instance of ProoftoolViewable[${T}].)" )
  trait ProoftoolViewable[-T] {
    def display( x: T, name: String ): Unit
  }

  object ProoftoolViewable {
    def apply[T: ProoftoolViewable] = implicitly[ProoftoolViewable[T]]
  }

  implicit val LKProofViewable: ProoftoolViewable[LKProof] =
    ( x, name ) => new LKProofViewer( name, x ).showFrame()

  implicit def SequentProofViewable[F, T <: SequentProof[F, T]](
    implicit
    notLK: Not[T <:< LKProof]
  ): ProoftoolViewable[SequentProof[F, T]] = {
    def renderer( x: F ): String = x match {
      case e: Expr => LatexExporter( e )
      case _       => x.toString
    }

    ( p, name ) => new SequentProofViewer( name, p, renderer ).showFrame()
  }

  implicit val ExpansionProofViewable: ProoftoolViewable[ExpansionProof] =
    ( ep, name ) => new ExpansionSequentViewer( name, ep.expansionSequent ).showFrame()

  implicit val ExpansionProofWithCutViewable: ProoftoolViewable[ExpansionProofWithCut] =
    ( ep, name ) => ProoftoolViewable[ExpansionProof].display( ep.expansionWithCutAxiom, name )

  implicit def StructViewable[D]: ProoftoolViewable[Struct[D]] =
    ( s, name ) => new StructViewer[D]( name, s ).showFrame()

  implicit val ListViewable: ProoftoolViewable[Iterable[HOLSequent]] =
    ( list, name ) => new ListViewer( name, list.toList ).showFrame()

  implicit val SequentViewable: ProoftoolViewable[HOLSequent] =
    ( seq, name ) => new ListViewer( name, List( seq ) ).showFrame()

  implicit val ProofDatabaseViewable: ProoftoolViewable[ExtendedProofDatabase] =
    ( db, _ ) =>
      for ( ( pName, p ) <- db.proofs )
        ProoftoolViewable[LKProof].display( p, pName )

  implicit def OptionViewable[T: ProoftoolViewable]: ProoftoolViewable[Option[T]] = {
    case ( Some( y ), name ) => ProoftoolViewable[T].display( y, name )
    case _                   => throw new IllegalArgumentException
  }

  implicit def EitherViewable[T: ProoftoolViewable, S]: ProoftoolViewable[Either[S, T]] = {
    case ( Right( y ), name ) => ProoftoolViewable[T].display( y, name )
    case ( Left( y ), _ )     => throw new IllegalArgumentException( y.toString )
  }
}
