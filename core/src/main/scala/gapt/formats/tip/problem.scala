package gapt.formats.tip

import gapt.expr._
import gapt.expr.hol.{ existentialClosure, universalClosure }
import gapt.proofs.{ Context, ImmutableContext, Sequent }

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
    "// Sorts\n" +
      compileSorts( problem ).mkString( "\n" ) + "\n\n" +
      "// Inductive types\n" +
      compileInductiveTypes( problem ).mkString( "\n\n" ) + "\n" +
      compileConstants( problem ) + "\n" +
      compileFunctionConstants( problem ) + "\n\n" +
      s"""|val sequent =
          |  hols\"\"\"
          |    ${
        ( compileProjectorDefinitions( problem ) ++
          compileFunctionDefinitions( problem ) ++
          compileConstructorInjectivityAxioms( problem ) ++
          compileProblemAssumptions( problem ) ) mkString ( "", ",\n    ", "" )
      }
          |    :-
          |    goal: ${stripNewlines( problem.goal.toString )}
          |  \"\"\"
      """.stripMargin
  }

  private def compileProblemAssumptions( problem: TipProblem ): Seq[String] = {
    problem.assumptions.zipWithIndex.map {
      case ( assumption, index ) => s"assumption_$index: ${stripNewlines( assumption.toString() )}"
    }
  }

  private def compileConstructorInjectivityAxioms( problem: TipProblem ): Seq[String] = {
    problem.constructorInjectivity.zipWithIndex.map {
      case ( axiom, index ) => s"constr_inj_$index: ${stripNewlines( universalClosure( axiom ).toString() )}"
    }
  }

  private def compileFunctionDefinitions( problem: TipProblem ): Seq[String] = {
    problem.functions.flatMap {
      function =>
        function.definitions.zipWithIndex.map {
          case ( definition, index ) =>
            s"def_${function.fun.name}_$index: ${stripNewlines( universalClosure( definition ).toString() )}"
        }
    }
  }

  private def compileProjectorDefinitions( problem: TipProblem ): Seq[String] = {
    val constructors = problem.datatypes.flatMap( _.constructors )
    ( constructors.flatMap( _.projectors ).map( _.name ) zip
      constructors.flatMap( _.projectorDefinitions ) ) map
      { case ( name, definition ) => s"def_$name: ${stripNewlines( universalClosure( definition ).toString() )}" }
  }

  private def compileFunctionConstants( problem: TipProblem ): String = {
    "\n//Function constants\n" +
      ( problem.functions map { f => "ctx += " + compileConst( f.fun ) } mkString ( "\n" ) )
  }

  private def compileConstants( problem: TipProblem ): String = {
    "\n//Constants\n" +
      ( "" )
  }

  private def compileInductiveTypes( problem: TipProblem ): Seq[String] = {
    problem.datatypes.tail map compileInductiveType
  }

  private def compileInductiveType( datatype: TipDatatype ): String = {
    val constructors = datatype.constructors.map { c => compileConst( c.constr ) } mkString ( ", " )
    val projectors = compileProjectors( datatype.constructors.flatMap( _.projectors ) )
    s"ctx += InductiveType(ty${"\"" + datatype.t.name + "\""}, ${constructors})" + "\n" + projectors
  }

  private def compileProjectors( projectors: Seq[Const] ): String = {
    projectors.map { compileProjector } mkString ( "", "\n", "" )
  }

  private def compileProjector( projector: Const ): String = {
    s"ctx += ${compileConst( projector )}"
  }

  private def compileSorts( problem: TipProblem ): Seq[String] =
    problem.sorts map {
      sort => s"ctx += TBase(${"\"" + sort.name + "\""})"
    }

  private def stripNewlines( s: String ): String =
    s.map( c => if ( c == '\n' ) ' ' else c )
}
