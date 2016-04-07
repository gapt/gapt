package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, instantiate, simplify }
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.{ InstanceTermEncoding, extractInstances }
import at.logic.gapt.proofs.lk.{ ExtractInterpolant, skolemize }
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS

import scala.io.StdIn

object Viper {

  def solve( problem: TipProblem ): LambdaExpression = {
    implicit var ctx = problem.context

    val sequent @ Sequent( theory, Seq( All.Block( vs, _ ) ) ) = problem.toSequent
    println( sequent )
    println()

    val paramTypes = vs.map( _.exptype ).map( _.asInstanceOf[TBase] )

    val pi1QTys = ctx.typeDefs.toSeq collect {
      case InductiveType( ty, _ ) if ty != To => ty
    }

    var instances = Set[Seq[LambdaExpression]]()
    while ( instances.size < 4 ) {
      instances += randomInstance.generate( paramTypes, 0 to 5 contains _ )
    }
    println( "Instances:" )
    for ( inst <- instances )
      println( inst map { _.toSigRelativeString } )
    println()

    // Compute many-sorted expansion sequents
    val instanceProofs = instances map { inst =>
      println( s"Proving instance ${inst.map( _.toSigRelativeString )}" )
      val instanceSequent = sequent.map( identity, instantiate( _, inst ) )
      if ( true ) {
        if ( false ) {
          val reduction = GroundingReductionET |> CNFReductionExpRes |> PredicateReductionCNF |> ErasureReductionCNF
          val ( erasedCNF, back ) = reduction forward instanceSequent
          val Some( erasedProof ) = SPASS getRobinsonProof erasedCNF
          val reifiedExpansion = back( erasedProof )
          inst -> reifiedExpansion
        } else {
          val reduction = GroundingReductionET |> ErasureReductionET
          val ( erasedInstanceSequent, back ) = reduction forward instanceSequent
          val erasedExpansion = SPASS getExpansionProof erasedInstanceSequent getOrElse {
            throw new IllegalArgumentException( s"Cannot prove:\n$erasedInstanceSequent" )
          }
          val reifiedExpansion = back( erasedExpansion )
          require( Z3 isValid reifiedExpansion.deep )
          inst -> reifiedExpansion
        }
      } else {
        inst -> Escargot.getExpansionProof( instanceSequent ).get
      }
    }
    println()

    instanceProofs foreach {
      case ( inst, es ) =>
        println( s"Instances for x = ${inst.map( _.toSigRelativeString )}:" )
        println( extractInstances( es ).map( _.toSigRelativeString ) )
        println()
    }

    val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, vs ) ) )

    val A = Const( "A", FunctionType( encoding.instanceTermType, paramTypes ) )

    val template = simplePi1RecSchemTempl( A( vs: _* ), pi1QTys )
    val ws = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w$i", t )
    println( "Recursion scheme template:" )
    template.template.toSeq.sortBy { _._1.toString } foreach println
    println()

    val targets = for ( ( inst, es ) <- instanceProofs; term <- encoding encode es ) yield A( inst: _* ) -> term
    val rs = template.findMinimalCover( targets, weight = rule => expressionSize( rule.lhs === rule.rhs ) )
    println( s"Minimized recursion scheme:\n$rs\n" )

    val logicalRS = encoding decode rs
    println( s"Logical recursion scheme:\n$logicalRS\n" )

    val inst = randomInstance.generate( paramTypes, 6 to 10 contains _ )
    val lang = logicalRS.parametricLanguage( inst: _* ) map { _.asInstanceOf[HOLFormula] }
    println( s"Checking validity for instance ${inst.map( _.toSigRelativeString )}" )
    require( Z3 isValid Or( lang ), s"Validity for instance ${inst.map( _.toSigRelativeString )}" )
    if ( false ) {
      val Some( lk ) = Escargot getLKProof Sequent( lang.toSeq map { case Neg( f ) => ( f, false ) case f => ( f, true ) } )
      println( "Interpolant of the instance sequent:" )
      println( simplify( ExtractInterpolant( lk, lk.conclusion.map( _ => false, _ => true ) )._3 ).toSigRelativeString )
    }
    println()

    val qbup @ Ex( x_G, qbupMatrix ) = qbupForRecSchem( logicalRS )
    println( s"QBUP:\n${qbup.toSigRelativeString}\n" )

    val canSolInst = randomInstance.generate( paramTypes, 3 to 5 contains _ )
    println( s"Canonical solution at G($canSolInst,w):" )
    val G_ = logicalRS.nonTerminals.find( _.name == "G" ).get
    val canSol = And( logicalRS generatedTerms G_( canSolInst: _* )( ws: _* ) map { -_ } )
    CNFp.toClauseList( canSol ).map { _.map { _.toSigRelativeString } } foreach println
    println()

    val Some( solution ) = hSolveQBUP( qbupMatrix, x_G( canSolInst: _* )( ws: _* ), canSol )
    println()

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    println( s"Solution: ${solution.toSigRelativeString}\n" )
    println( Z3 isValid skolemize( formula ) )

    solution
  }

  def main( args: Array[String] ): Unit = args match {
    case Array( fn ) =>
      solve( TipSmtParser fixupAndParseFile fn )
    case Array() =>
      solve( TipSmtParser fixupAndParse Stream.continually( StdIn.readLine() ).takeWhile( _ != null ).mkString )
  }

}
