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
    def display( x: T, name: String ): List[ProofToolViewer[_]]
  }

  object ProoftoolViewable {
    def apply[T: ProoftoolViewable] = implicitly[ProoftoolViewable[T]]
  }

  implicit val LKProofViewable: ProoftoolViewable[LKProof] =
    ( x, name ) => List( new LKProofViewer( name, x ) )

  implicit def SequentProofViewable[F, T <: SequentProof[F, T]](
    implicit
    notLK: Not[T <:< LKProof]
  ): ProoftoolViewable[SequentProof[F, T]] = {
    def renderer( x: F ): String = x match {
      case e: Expr => LatexExporter( e )
      case _       => x.toString
    }

    ( p, name ) => List( new SequentProofViewer( name, p, renderer ) )
  }

  implicit val ExpansionProofViewable: ProoftoolViewable[ExpansionProof] =
    ( ep, name ) => List( new ExpansionSequentViewer( name, ep.expansionSequent ) )

  implicit val ExpansionProofWithCutViewable: ProoftoolViewable[ExpansionProofWithCut] =
    ( ep, name ) => ProoftoolViewable[ExpansionProof].display( ep.expansionWithCutAxiom, name )

  implicit def StructViewable[D]: ProoftoolViewable[Struct[D]] =
    ( s, name ) => List( new StructViewer[D]( name, s ) )

  implicit val ListViewable: ProoftoolViewable[Iterable[HOLSequent]] =
    ( list, name ) => List( new ListViewer( name, list.toList ) )

  implicit val SequentViewable: ProoftoolViewable[HOLSequent] =
    ( seq, name ) => List( new ListViewer( name, List( seq ) ) )

  implicit val ProofDatabaseViewable: ProoftoolViewable[ExtendedProofDatabase] =
    ( db, _ ) => db.proofs.flatMap( ( t ) => ProoftoolViewable[LKProof].display( t._2, t._1 ) )

  implicit def OptionViewable[T: ProoftoolViewable]: ProoftoolViewable[Option[T]] = ( oT: Option[T], name: String ) => oT.toList.flatMap( ProoftoolViewable[T].display( _, name ) )

  implicit def EitherViewable[T: ProoftoolViewable, S]: ProoftoolViewable[Either[S, T]] = ( oT: Either[S, T], name: String ) => oT.toOption.toList.flatMap( ProoftoolViewable[T].display( _, name ) )
}
