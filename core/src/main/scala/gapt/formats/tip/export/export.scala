package gapt.formats.tip.export

import gapt.expr.Const
import gapt.expr.formula.And
import gapt.expr.formula.Formula
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.formula.constants.ImpC
import gapt.expr.formula.constants.NegC
import gapt.expr.formula.constants.OrC
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty
import gapt.formats.tip.TipConstructor
import gapt.formats.tip.TipDatatype
import gapt.formats.tip.TipProblem
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.toSExpression
import gapt.formats.tip.util.TipNameGenerator
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.facet.Definitions
import gapt.proofs.context.facet.StructurallyInductiveTypes
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.utils.Doc

package object export {

  def export( problem: TipSmtProblem ): Doc = {
    Doc.stack( toSExpression( problem ).map { _.toDoc } )
  }

  def export( problem: TipProblem ): Doc = {
    val problemDoc = Doc.stack( toSExpression( problem ).map { _.toDoc } )
    addInfoHeaderToProblem( problem.info, problemDoc )
  }

  private def addInfoHeaderToProblem( maybeInfo: Option[String], doc: Doc ) =
    maybeInfo match {
      case Some( info ) => commentDocument( info ) </> doc
      case _            => doc
    }

  private def commentDocument( comment: String ): Doc =
    Doc.stack( commentLines( comment ) )

  private def commentLines( comment: String ): Seq[Doc] =
    comment.split( "\n" ).map { "; " ++ _ }.map { Doc.text } toSeq

  /**
   * Encodes the given sequent and context in TIP SMT2 format.
   *
   * Since the datatypes specified in the context do not have explicit
   * destructors this conversion introduces new destructor symbols of the form
   * 'p_<n>', where n is a natural number.
   *
   * @param sequent The sequent to be encoded.
   * @param context The context to be encoded.
   * @return A document that represents the SMT2 encoding of the sequent and
   * the context.
   */
  def export( sequent: Sequent[Formula], context: Context, comment: Option[String] = None ): Doc = {
    export(
      new SequentContextToTipProblemConverter( sequent, context, comment ).convert )
  }

  def export( sequent: HOLSequent )(
    implicit
    ctx: Context, dummyImplicit: DummyImplicit ): Doc =
    export( sequent, ctx )

  def export( formula: Formula )(
    implicit
    ctx: Context ): Doc =
    export( Sequent() :+ formula )

  private class SequentContextToTipProblemConverter(
      sequent: Sequent[Formula],
      context: Context,
      comment: Option[String]   = None ) {

    private def contextSymbols( context: Context ): Set[String] = {
      context.constants.map { _.name }.toSet ++
        context.get[BaseTypes].baseTypes.keys.toSet
    }

    private def toTipDatatype(
      structurallyInductiveType: ( String, Vector[Const] ) ): TipDatatype = {

      val ( typeName, constructors ) = structurallyInductiveType

      val tipConstructors = constructors.map {
        constructor =>
          val FunctionType( _, argumentTypes ) = constructor.ty
          TipConstructor(
            constructor,
            argumentTypes.map {
              at =>
                Const(
                  nameGenerator.fresh( "p" ),
                  TBase( typeName ) ->: at )
            } )
      }
      TipDatatype( TBase( typeName ), tipConstructors )
    }

    private val nameGenerator: TipNameGenerator =
      new TipNameGenerator( contextSymbols( context ) ++ Set( "p" ) )

    def convert: TipProblem = {
      val assertions = sequent.antecedent
      val goal = And( sequent.succedent )
      val datatypes =
        context.get[StructurallyInductiveTypes]
          .constructors
          .filter {
            case ( name, _ ) => name != "o"
          }
          .map { toTipDatatype }
          .toSeq

      val sorts =
        context
          .get[BaseTypes]
          .baseTypes
          .keys
          .toSet
          .diff(
            context
              .get[StructurallyInductiveTypes]
              .constructors
              .keys
              .toSet )
          .map { TBase( _, List[Ty]() ) }
          .toSeq

      val constants =
        context
          .constants
          .toSet
          .diff(
            context
              .get[StructurallyInductiveTypes]
              .constructors
              .values
              .flatten
              .toSet )
          .diff( Set(
            NegC(),
            AndC(),
            OrC(),
            ImpC(),
            ForallC( TVar( "x" ) ),
            ExistsC( TVar( "x" ) ),
            EqC( TVar( "x" ) ) ) )
          .diff( context.get[SkolemFunctions].skolemDefs.keySet )
          .filter {
            c =>
              !context.get[Definitions].definitions.keySet.contains( c.name )
          }

      TipProblem(
        context.toImmutable,
        Nil,
        sorts,
        datatypes,
        constants.toSeq,
        Seq(),
        assertions,
        goal,
        comment )
    }

  }
}
