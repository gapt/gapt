package at.logic.gapt.formats.tip

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ existentialClosure, universalClosure }
import at.logic.gapt.proofs.{ Context, ImmutableContext, Sequent }

case class TipConstructor( constr: Const, projectors: Seq[Const] ) {
  val FunctionType( datatype, fieldTypes ) = constr.ty
  require( fieldTypes.size == projectors.size )
  projectors foreach { case Const( _, FunctionType( to, from ), _ ) => require( from == Seq( datatype ) ) }

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

object tipScalaEncoding {

  private def compileConst( const: Const ): String = {
    "hoc" + "\"" + stripNewlines( "'" + const.name + "' :" + const.ty.toString ) + "\""
  }

  def apply( problem: TipProblem ): String = {
    compileSorts( problem ) + "\n" +
      compileInductiveTypes( problem ) + "\n" +
      compileConstants( problem ) + "\n" +
      compileFunctionConstants( problem ) + "\n\n" +
      s"""|val sequent =
          |  hols\"\"\"
          |    ${( problem.datatypes.flatMap( _.constructors ).flatMap( _.projectors ).map( _.name ) zip problem.datatypes.flatMap( _.constructors ).flatMap( _.projectorDefinitions ) ) map { case ( n, d ) => s"def_$n: ${stripNewlines( universalClosure( d ).toString() )}" } mkString ( ",\n" )},
          |    ${problem.functions.flatMap { f => f.definitions.zipWithIndex.map { case ( d, i ) => s"def_${f.fun.name}_$i: ${stripNewlines( universalClosure( d ).toString() )}" } } mkString ( "", ",\n", "" )},
          |    ${problem.constructorInjectivity.zipWithIndex.map { case ( ci, i ) => s"constr_inj_$i: ${stripNewlines( universalClosure( ci ).toString() )}" } mkString ( "", ",\n", "" )}
          |    ${problem.assumptions.zipWithIndex.map { case ( a, i ) => s"assumption_$i: ${stripNewlines( a.toString() )}" } mkString ( "", ",\n", "" )}
          |    :-
          |    goal: ${stripNewlines( problem.goal.toString )}
          |  \"\"\"
      """.stripMargin
  }

  private def compileFunctionConstants( problem: TipProblem ): String = {
    "\n//Function constants\n" +
      ( problem.functions map { f => "ctx += " + compileConst( f.fun ) } mkString ( "\n" ) )
  }

  private def compileConstants( problem: TipProblem ): String = {
    "\n//Constants\n" +
      ( "" )
  }

  private def compileInductiveTypes( problem: TipProblem ): String = {
    "\n// Inductive types\n" +
      ( problem.datatypes.tail map ( compileInductiveType ) mkString ( "\n" ) )
  }

  private def compileInductiveType( datatype: TipDatatype ): String = {
    s"ctx += InductiveType(ty${"\"" + datatype.t.name + "\""}, ${datatype.constructors.map { c => compileConst( c.constr ) } mkString ( ", " )})" + "\n" +
      compileProjectors( datatype.constructors.flatMap( _.projectors ) )
  }

  private def compileProjectors( projectors: Seq[Const] ): String = {
    projectors.map { compileProjector } mkString ( "", "\n", "" )
  }

  private def compileProjector( projector: Const ): String = {
    s"ctx += ${compileConst( projector )}"
  }

  private def compileSorts( problem: TipProblem ): String = {
    "// Sorts\n" +
      ( problem.sorts map { sort => s"ctx += TBase(${"\"" + sort.name + "\""})" } mkString ( "\n" ) )
  }

  private def stripNewlines( s: String ): String =
    s.map( c => if ( c == '\n' ) ' ' else c )
}