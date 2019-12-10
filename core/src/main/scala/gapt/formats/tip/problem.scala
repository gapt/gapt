package gapt.formats.tip

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Top
import gapt.expr.formula.hol.existentialClosure
import gapt.expr.formula.hol.universalClosure
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.util.ConditionalReductionRule
import gapt.expr.util.LambdaPosition
import gapt.expr.util.freeVariables
import gapt.logic
import gapt.logic.projectorDefinitions
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.update.InductiveType

case class TipFun( fun: Const, definitions: Seq[Formula] )

case class TipProblem(
    ctx:                 ImmutableContext,
    definitions:         Seq[Formula],
    sorts:               Seq[TBase],
    datatypes:           Seq[InductiveType],
    uninterpretedConsts: Seq[Const],
    functions:           Seq[TipFun],
    assumptions:         Seq[Formula],
    goal:                Formula ) {

  private val BOOL2: TBase = TBase( "Bool2" )

  val constructorDisjointness: Seq[Formula] =
    datatypes.filter( _.baseType != To ).flatMap( logic.disjointnessAxioms )

  val constructorInjectivity: Seq[Formula] =
    datatypes.flatMap( logic.injectivityAxioms )

  val projectorDefinitions: Seq[Formula] =
    datatypes.flatMap( logic.projectorDefinitions )

  val projectorDefinitionRules: Seq[ConditionalReductionRule] =
    datatypes.flatMap( logic.projectorDefinitionRules )
      .map( ConditionalReductionRule( _ ) )

  def toSequent: HOLSequent = {
    val bool2Axioms = {
      implicit val c = ctx
      if ( ctx.isType( BOOL2 ) ) {
        Seq( hof"!x (x = True | x = False)" )
      } else {
        Seq()
      }
    }
    existentialClosure(
      bool2Axioms ++:
        projectorDefinitions ++:
        definitions ++:
        functions.flatMap( _.definitions ) ++:
        constructorDisjointness ++:
        assumptions ++:
        Sequent()
        :+ goal )
  }

  def context: ImmutableContext = ctx

  def reductionRules: Seq[ConditionalReductionRule] = {
    val definitionReductionRules = definitions.flatMap {
      case All.Block( _, Eq( lhs @ Apps( Const( _, _, _ ), _ ), rhs ) ) =>
        Some( ConditionalReductionRule( Nil, lhs, rhs ) )
      case All.Block( _, Neg( lhs @ Atom( _, _ ) ) ) =>
        Some( ConditionalReductionRule( Nil, lhs, Bottom() ) )
      case All.Block( _, lhs @ Atom( _, _ ) ) =>
        Some( ConditionalReductionRule( Nil, lhs, Top() ) )
      case _ => None
    }

    val bool2ReductionRules = {
      implicit val c = ctx
      if ( ctx.isType( BOOL2 ) ) {
        ConditionalReductionRule( Nil, hof"True = False", hof"⊥" ) ::
          ConditionalReductionRule( Nil, hof"False = True", hof"⊥" ) :: Nil
      } else {
        Nil
      }
    }

    bool2ReductionRules ++
      functionDefinitionReductionRules ++
      projectorDefinitionRules ++
      definitionReductionRules :+
      ConditionalReductionRule( Nil, le"x = x", le"⊤" ) :+
      ConditionalReductionRule( Nil, hof"¬ ⊥", hof"⊤" ) :+
      ConditionalReductionRule( Nil, hof"¬ ⊤", hof"⊥" )

  }

  private val functionDefinitionReductionRules: Seq[ConditionalReductionRule] = {
    functions.flatMap { _.definitions }.flatMap {
      case All.Block( _, Imp.Block( cs, Eq( lhs @ Apps( _: Const, _ ), rhs ) ) ) if isReductionRule( cs, lhs, rhs ) =>
        Some( ConditionalReductionRule( cs, lhs, rhs ) )
      case All.Block( _, Imp.Block( cs, Neg( lhs @ Atom( _, _ ) ) ) ) if isReductionRule( cs, lhs, Bottom() ) =>
        Some( ConditionalReductionRule( cs, lhs, Bottom() ) )
      case All.Block( _, Imp.Block( cs, lhs @ Atom( _, _ ) ) ) if isReductionRule( cs, lhs, Top() ) =>
        Some( ConditionalReductionRule( cs, lhs, Top() ) )
      case All.Block( _, Imp.Block( cs, Iff( lhs, rhs ) ) ) if isReductionRule( cs, lhs, rhs ) =>
        Some( ConditionalReductionRule( cs, lhs, rhs ) )
      case _ => None
    }
  }

  private def isReductionRule( cs: Seq[Formula], lhs: Expr, rhs: Expr ): Boolean = {
    ( cs.flatMap { freeVariables( _ ) } ++ freeVariables( rhs ) ).toSet.subsetOf( freeVariables( lhs ) ) &&
      !lhs.isInstanceOf[Var]
  }

  override def toString: String = toSequent.toSigRelativeString( context )
}

object subterms {
  def apply( e: Expr ): Seq[( Expr, LambdaPosition )] = {
    subterms( e, LambdaPosition() ).map {
      case ( t, LambdaPosition( ps ) ) => t -> LambdaPosition( ps.reverse )
    }
  }
  private def apply( e: Expr, position: LambdaPosition ): Seq[( Expr, LambdaPosition )] = {
    val LambdaPosition( xs ) = position
    ( e -> position ) +: ( e match {
      case Abs( _, e1 ) =>
        subterms( e1, LambdaPosition( LambdaPosition.Left :: xs ) )
      case App( e1, e2 ) =>
        subterms( e1, LambdaPosition( LambdaPosition.Left +: xs ) ) ++ subterms( e2, LambdaPosition( LambdaPosition.Right +: xs ) )
      case _ => Seq()
    } )
  }
}

trait TipProblemDefinition {
  def sorts: Seq[TBase]
  def datatypes: Seq[InductiveType]
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
          if ( !ctx.isType( dt.baseType ) ) {
            ctx += dt
          }
          val projectors = dt.constructors.flatMap {
            _.fields.flatMap( _.projector )
          }
          projectors.foreach { ctx += _ }
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
    TipProblem( ctx, Nil, sorts, datatypes, uninterpretedConsts, functions, assumptions, goal )
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
    problem.constructorDisjointness.zipWithIndex.map {
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
    val definitions = problem.datatypes.flatMap( projectorDefinitions )
    definitions.map { d =>
      val All.Block( _, Eq( Apps( p: Const, _ ), _ ) ) = d
      s"def_${
        p.name.map { c => if ( c == '-' ) '_' else c }
      }: ${
        stripNewlines( d.toString() )
      }"
    }
  }

  private def compileFunctionConstants( problem: TipProblem ): String = {
    "\n//Function constants\n" +
      ( problem.functions map { f => "ctx += " + compileConst( f.fun ) } mkString ( "\n" ) )
  }

  private def compileInductiveTypes( problem: TipProblem ): Seq[String] = {
    problem.datatypes.tail map compileInductiveType
  }

  private def compileInductiveType( datatype: InductiveType ): String = {
    val constructors = datatype.constructorConstants.map { c => compileConst( c ) } mkString ( ", " )
    val projectors = compileProjectors( datatype.constructors.flatMap( _.fields.flatMap( _.projector ) ) )
    s"ctx += InductiveType(ty${"\"" + datatype.baseType.name + "\""}, ${constructors})" + "\n" + projectors
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
