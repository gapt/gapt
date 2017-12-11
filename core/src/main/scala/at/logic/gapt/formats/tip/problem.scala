package at.logic.gapt.formats.tip

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existentialClosure, universalClosure }
import at.logic.gapt.proofs.{ Context, ImmutableContext, Sequent }

case class TipConstructor( constr: Const, projectors: Seq[Const] ) {
  val FunctionType( datatype, fieldTypes ) = constr.ty
  require( fieldTypes.size == projectors.size )
  projectors foreach { case Const( _, FunctionType( to, from ) ) => require( from == Seq( datatype ) ) }

  def arity = projectors size

  def projectorDefinitions: Seq[Formula] = {
    val fieldVars = fieldTypes.zipWithIndex.map { case ( t, i ) => Var( s"x$i", t ) }
    ( projectors, fieldVars ).zipped map { ( p, f ) => p( constr( fieldVars: _* ) ) === f }
  }
}
case class TipDatatype( t: TBase, constructors: Seq[TipConstructor] ) {
  constructors foreach { ctr => require( ctr.datatype == t ) }
}

case class TipFun( fun: Const, definitions: Seq[Formula] )

case class TipProblem(
    ctx:   ImmutableContext,
    sorts: Seq[TBase], datatypes: Seq[TipDatatype],
    uninterpretedConsts: Seq[Const], functions: Seq[TipFun],
    assumptions: Seq[Formula], goal: Formula ) {
  def constructorInjectivity =
    for {
      TipDatatype( ty, ctrs ) <- datatypes
      if ty != To // FIXME
      ( TipConstructor( ctr1, _ ), i1 ) <- ctrs.zipWithIndex
      ( TipConstructor( ctr2, _ ), i2 ) <- ctrs.zipWithIndex
      if i1 < i2 // ignore symmetric pairs
      FunctionType( _, args1 ) = ctr1.ty
      FunctionType( _, args2 ) = ctr2.ty
    } yield universalClosure(
      ctr1( ( for ( ( t, j ) <- args1.zipWithIndex ) yield Var( s"x$j", t ) ): _* ) !==
        ctr2( ( for ( ( t, j ) <- args2.zipWithIndex ) yield Var( s"y$j", t ) ): _* ) )

  def toSequent = existentialClosure(
    datatypes.flatMap( _.constructors ).flatMap( _.projectorDefinitions ) ++:
      functions.flatMap( _.definitions ) ++:
      constructorInjectivity ++:
      assumptions ++:
      Sequent()
      :+ goal )

  def context: ImmutableContext = ctx

  override def toString: String = toSequent.toSigRelativeString( context )
}

trait TipProblemDefinition {
  def sorts: Seq[TBase]
  def datatypes: Seq[TipDatatype]
  def uninterpretedConsts: Seq[Const]
  def assumptions: Seq[Formula]
  def functions: Seq[TipFun]
  def goal: Formula
  def loadProblem: TipProblem = {
    var ctx = Context()
    sorts foreach { ctx += _ }
    datatypes foreach {
      dt =>
        {
          if ( !ctx.isType( dt.t ) ) {
            ctx += Context.InductiveType( dt.t, dt.constructors.map( _.constr ): _* )
          }
          dt.constructors.foreach { ctr => ctr.projectors.foreach { ctx += _ } }
        }
    }
    uninterpretedConsts foreach { constant =>
      if ( ctx.constant( constant.name ).isEmpty ) {
        ctx += constant
      }
    }
    functions foreach { function =>
      ctx += function.fun
    }
    TipProblem( ctx, sorts, datatypes, uninterpretedConsts, functions, assumptions, goal )
  }
}
