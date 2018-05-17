package gapt.formats.tip.analysis

import gapt.formats.tip.parser._

object retrieveDatatypes {
  def apply( problemAst: TipSmtProblem ): Seq[TipSmtDatatype] = {
    problemAst.definitions flatMap {
      _ match {
        case TipSmtDatatypesDeclaration( datatypes ) => datatypes
        case _                                       => Seq()
      }
    }
  }
  def apply( problemAst: TipSmtProblem, datatype: String ): TipSmtDatatype = {
    println( datatype )
    apply( problemAst ).find( _.name == datatype ).get
  }
}

case class Type(
    argumentTypes: Seq[Datatype],
    returnType:    Datatype )

case class SymbolTable( problem: TipSmtProblem ) {

  private val symbols: Map[String, Type] = computeSymbols()

  def typeOf( symbol: String ): Type = symbols( symbol )
  def contains( symbol: String ): Boolean = symbols.contains( symbol )

  private def computeSymbols(): Map[String, Type] = {

    var symbols: Map[String, Type] = Map()

    problem.definitions foreach {
      _ match {
        case TipSmtFunctionDeclaration(
          functionName, _, argumentTypes, returnType
          ) =>
          val argTypes = argumentTypes.map {
            argType => Datatype( argType.typename )
          }
          symbols +=
            ( functionName ->
              Type( argTypes, Datatype( returnType.typename ) ) )

        case TipSmtFunctionDefinition(
          functionName, _, formalParameters, returnType, _
          ) =>
          val argTypes = formalParameters map { param =>
            Datatype( param.typ.typename )
          }
          symbols +=
            ( functionName ->
              Type( argTypes, Datatype( returnType.typename ) ) )

        case TipSmtConstantDeclaration( constantName, _, typ ) =>
          symbols += ( constantName -> Type( Seq(), Datatype( typ.typename ) ) )

        case TipSmtDatatypesDeclaration( datatypes ) =>
          datatypes.foreach {
            symbols ++= datatypeSymbols( _ )
          }

        case _ =>
      }
    }
    symbols
  }

  private def datatypeSymbols(
    tipSmtDatatype: TipSmtDatatype ): Map[String, Type] = {
    val symbols: Seq[( String, Type )] =
      tipSmtDatatype.constructors map {
        case TipSmtConstructor( constructorName, _, fields ) =>
          val fieldTypes: Seq[Datatype] = fields map {
            field => Datatype( field.typ.typename )
          }
          constructorName -> Type(
            fieldTypes, Datatype( tipSmtDatatype.name ) )
      }
    Map( symbols: _* )
  }
}