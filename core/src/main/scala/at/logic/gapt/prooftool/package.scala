package at.logic.gapt

import at.logic.gapt.expr.{ HOLFormula, LambdaExpression }
import at.logic.gapt.formats.latex.LatexExporter
import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.proofs.expansion.{ ExpansionProof, ExpansionProofWithCut }
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ HOLSequent, SequentProof }
import at.logic.gapt.utils.Not

import scala.annotation.implicitNotFound
import scalaz.{ -\/, \/, \/- }

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

  /**
   * Creates an instance of the ProoftoolViewable typeclass from a function.
   */
  def instance[T]( disp: ( T, String ) => Unit ): ProoftoolViewable[T] = new ProoftoolViewable[T] {
    override def display( x: T, name: String ) = disp( x, name )
  }

  implicit val LKProofViewable: ProoftoolViewable[LKProof] = instance { ( x: LKProof, name: String ) =>
    new LKProofViewer( name, x ).showFrame()
  }

  implicit def SequentProofViewable[F, T <: SequentProof[F, T]](
    implicit
    notLK: Not[T <:< LKProof]
  ) = instance { ( p: SequentProof[F, T], name: String ) =>
    def renderer( x: F ): String = x match {
      case e: LambdaExpression => LatexExporter( e )
      case _                   => x.toString
    }
    new SequentProofViewer( name, p, renderer ).showFrame()
  }

  implicit val ExpansionProofViewable: ProoftoolViewable[ExpansionProof] = instance { ( ep: ExpansionProof, name: String ) =>
    new ExpansionSequentViewer( name, ep.expansionSequent ).showFrame()
  }

  implicit val ExpansionProofWithCutViewable: ProoftoolViewable[ExpansionProofWithCut] = instance { ( ep: ExpansionProofWithCut, name: String ) =>
    ProoftoolViewable[ExpansionProof].display( ep.expansionWithCutAxiom, name )
  }

  implicit def StructViewable[D] = instance { ( s: Struct[D], name: String ) =>
    new StructViewer[D]( name, s ).showFrame()
  }

  implicit val ListViewable: ProoftoolViewable[Iterable[HOLSequent]] = instance { ( list: Iterable[HOLSequent], name: String ) =>
    new ListViewer( name, list.toList ).showFrame()
  }

  implicit val SequentViewable: ProoftoolViewable[HOLSequent] = instance { ( seq: HOLSequent, name: String ) =>
    new ListViewer( name, List( seq ) ).showFrame()
  }

  implicit val ProofDatabaseViewable: ProoftoolViewable[ExtendedProofDatabase] = instance { ( db: ExtendedProofDatabase, name: String ) =>
    for ( ( pName, p ) <- db.proofs )
      ProoftoolViewable[LKProof].display( p, pName )
  }

  implicit def OptionViewable[T: ProoftoolViewable] = instance { ( x: Option[T], name: String ) =>
    x match {
      case Some( y ) => ProoftoolViewable[T].display( y, name )
      case None      => throw new IllegalArgumentException
    }
  }

  implicit def DisjViewable[T: ProoftoolViewable, S] = instance { ( x: \/[S, T], name: String ) =>
    x match {
      case \/-( y ) => ProoftoolViewable[T].display( y, name )
      case -\/( y ) => throw new IllegalArgumentException( y.toString )
    }
  }

  implicit def EitherViewable[T: ProoftoolViewable, S] = instance { ( x: Either[S, T], name: String ) =>
    x match {
      case Right( y ) => ProoftoolViewable[T].display( y, name )
      case Left( y )  => throw new IllegalArgumentException( y.toString )
    }
  }
}
