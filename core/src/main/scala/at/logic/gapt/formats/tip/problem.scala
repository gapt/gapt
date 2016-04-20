package at.logic.gapt.formats.tip

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existsclosure, univclosure }
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }

case class TipConstructor( constr: Const, projectors: Seq[Const] ) {
  val FunctionType( datatype, fieldTypes ) = constr.exptype
  require( fieldTypes.size == projectors.size )
  projectors foreach { case Const( _, FunctionType( to, from ) ) => require( from == Seq( datatype ) ) }

  def arity = projectors size

  def projectorDefinitions: Seq[HOLFormula] = {
    val fieldVars = fieldTypes.zipWithIndex.map { case ( t, i ) => Var( s"x$i", t ) }
    ( projectors, fieldVars ).zipped map { ( p, f ) => p( constr( fieldVars: _* ) ) === f }
  }
}
case class TipDatatype( t: TBase, constructors: Seq[TipConstructor] ) {
  constructors foreach { ctr => require( ctr.datatype == t ) }
}

case class TipFun( fun: Const, definitions: Seq[HOLFormula] )

case class TipProblem(
    sorts: Seq[TBase], datatypes: Seq[TipDatatype],
    uninterpretedConsts: Seq[Const], functions: Seq[TipFun],
    assumptions: Seq[HOLFormula], goal: HOLFormula
) {
  def constructorInjectivity =
    for {
      TipDatatype( ty, ctrs ) <- datatypes
      if ty != To // FIXME
      ( TipConstructor( ctr1, _ ), i1 ) <- ctrs.zipWithIndex
      ( TipConstructor( ctr2, _ ), i2 ) <- ctrs.zipWithIndex
      if i1 < i2 // ignore symmetric pairs
      FunctionType( _, args1 ) = ctr1.exptype
      FunctionType( _, args2 ) = ctr2.exptype
    } yield univclosure(
      ctr1( ( for ( ( t, j ) <- args1.zipWithIndex ) yield Var( s"x$j", t ) ): _* ) !==
        ctr2( ( for ( ( t, j ) <- args2.zipWithIndex ) yield Var( s"y$j", t ) ): _* )
    )

  def toSequent = existsclosure(
    datatypes.flatMap( _.constructors ).flatMap( _.projectorDefinitions ) ++:
      functions.flatMap( _.definitions ) ++:
      constructorInjectivity ++:
      assumptions ++:
      Sequent()
      :+ goal
  )

  def context =
    FiniteContext(
      constants = Set() ++ uninterpretedConsts ++ functions.map { _.fun } ++
      datatypes.flatMap { _.constructors }.flatMap { c => c.projectors :+ c.constr },
      definitions = Map(),
      typeDefs = Set() ++ sorts.map { Context.Sort( _ ) } ++
        datatypes.map { dt => Context.InductiveType( dt.t, dt.constructors.map { _.constr } ) }
    )
}
