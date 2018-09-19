package gapt.formats.tip.export

import gapt.expr.hol.SkolemFunctions
import gapt.expr.And
import gapt.expr.AndC
import gapt.expr.Const
import gapt.expr.EqC
import gapt.expr.ExistsC
import gapt.expr.ForallC
import gapt.expr.Formula
import gapt.expr.FunctionType
import gapt.expr.ImpC
import gapt.expr.NegC
import gapt.expr.OrC
import gapt.expr.TBase
import gapt.expr.TVar
import gapt.expr.Ty
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.toSExpression
import gapt.formats.tip.util.TipNameGenerator
import gapt.formats.tip.TipConstructor
import gapt.formats.tip.TipDatatype
import gapt.formats.tip.TipProblem
import gapt.proofs.Context.Definitions
import gapt.proofs.{ Context, HOLSequent, Sequent }
import gapt.utils.Doc

package object export {

  def export( problem: TipSmtProblem ): Doc = {
    Doc.stack( toSExpression( problem ).map { _.toDoc } )
  }

  def export( problem: TipProblem ): Doc = {
    Doc.stack( toSExpression( problem ).map { _.toDoc } )
  }

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
  def export( sequent: Sequent[Formula], context: Context ): Doc = {
    export(
      new SequentContextToTipProblemConverter( sequent, context ).convert )
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
      context: Context ) {

    private def contextSymbols( context: Context ): Set[String] = {
      context.constants.map { _.name }.toSet ++
        context.get[Context.BaseTypes].baseTypes.keys.toSet
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
        context.get[Context.StructurallyInductiveTypes]
          .constructors
          .filter {
            case ( name, _ ) => name != "o"
          }
          .map { toTipDatatype }
          .toSeq

      val sorts =
        context
          .get[Context.BaseTypes]
          .baseTypes
          .keys
          .toSet
          .diff(
            context
              .get[Context.StructurallyInductiveTypes]
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
              .get[Context.StructurallyInductiveTypes]
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
        sorts,
        datatypes,
        constants.toSeq,
        Seq(),
        assertions,
        goal )
    }

  }
}
