package gapt.provers.verit

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.ty.FunctionType
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.formats.verit.alethe.AletheException
import gapt.formats.verit.alethe.AletheProof
import gapt.formats.verit.alethe.Assume
import gapt.formats.verit.alethe.Step
import gapt.formats.verit.alethe._
import gapt.logic.EqualityReflexivity
import gapt.logic.EqualityTransitivity
import gapt.logic.FunctionCongruence
import gapt.logic.PredicateCongruence
import gapt.provers.verit.alethe.toExpr
import gapt.utils.shortestPath
import gapt.utils.symmetricClosure

object aletheQfUf {

  def collectUsedInputFormulas( proof: AletheProof, conversionTable: Map[String, Const] ): Seq[Formula] = {
    val usedLabels = collectUsedLabels( proof )
    collectInputs( proof )
      .filter { i => usedLabels.contains( i.label ) }
      .map { _.formula }
      .map { toExpr( _, Some( To ), conversionTable ) }
      .map { _.asInstanceOf[Formula] }
  }

  private def collectInputs( proof: AletheProof ): List[Assume] = {
    proof.steps.filter { _.isInstanceOf[Assume] }.map { _.asInstanceOf[Assume] }
  }

  def collectUsedLabels( proof: AletheProof ): Set[String] = {
    proof.steps.foldRight( proof.steps.last.premises.toSet ) {
      case ( command, usedLabels ) =>
        command match {
          case Step( _, label, _, premises, _ ) =>
            usedLabels ++ ( if ( usedLabels.contains( label ) ) premises else Set() )
          case _ => usedLabels
        }
    }
  }

  def collectEqualityInstances( proof: AletheProof, renaming: Map[String, Const] ): Set[FormulaInstance] = {
    predicateCongruenceInstances( proof, renaming ) ++
      functionCongruenceInstances( proof, renaming ) ++
      transitivityInstances( proof, renaming ) ++
      reflexivityInstances( proof, renaming )
  }

  private case class PredicateCongruenceInstance( predicate: Const, arguments: List[( Expr, Expr )] )

  def predicateCongruenceInstances( proof: AletheProof, renaming: Map[String, Const] ): Set[FormulaInstance] = {
    collectPredicateCongruenceInstances( proof )( renaming ).map {
      case PredicateCongruenceInstance( p, ts ) =>
        FormulaInstance( PredicateCongruence.formula( p ), ts.map { _._1 } ++ ts.map { _._2 } )
    }
  }

  private def collectPredicateCongruenceInstances(
    proof: AletheProof )(
    renaming: Map[String, Const] ): Set[PredicateCongruenceInstance] = {
    proof.steps.collect {
      case Step( "eq_congruent_pred", _, clause, _, _ ) =>
        val Apps( p2: Const, bs ) = toExpr( clause.last, Some( To ), renaming ) match {
          case Neg( f ) => f
          case f        => f
        }
        val Apps( p1: Const, as ) = toExpr( clause( clause.size - 2 ), Some( To ), renaming ) match {
          case Neg( f ) => f
          case f        => f
        }
        require( p1 == p2 )
        require( as.size == bs.size )
        PredicateCongruenceInstance( p1, as.zip( bs ) )
    }.toSet
  }

  private case class FunctionCongruenceInstance( function: Const, arguments: List[( Expr, Expr )] )

  def functionCongruenceInstances( proof: AletheProof, renaming: Map[String, Const] ): Set[FormulaInstance] = {
    collectFunctionCongruenceInstances( proof )( renaming ).map {
      case FunctionCongruenceInstance( f, as ) =>
        FormulaInstance( FunctionCongruence.formula( f ), as.map { _._1 } ++ as.map { _._2 } )
    }
  }

  private def collectFunctionCongruenceInstances(
    proof: AletheProof )(
    renaming: Map[String, Const] ): Set[FunctionCongruenceInstance] =
    proof.steps.collect {
      case Step( "eq_congruent", _, clause, _, _ ) =>
        val Eq( Apps( f1: Const, as ), Apps( _: Const, bs ) ) =
          toExpr( clause.last, Some( To ), renaming )
        FunctionCongruenceInstance( f1, as.zip( bs ) )
    }.toSet

  case class TransitivityInstance( t1: Expr, t2: Expr, t3: Expr )

  def transitivityInstances( proof: AletheProof, renaming: Map[String, Const] ): Set[FormulaInstance] = {
    collectTransitivityInstances( proof )( renaming ) map {
      case TransitivityInstance( t1, t2, t3 ) =>
        FormulaInstance( EqualityTransitivity.formula( t1.ty ), Seq( t1, t2, t3 ) )
    }
  }

  private def collectTransitivityInstances( proof: AletheProof )( renaming: Map[String, Const] ): Set[TransitivityInstance] = {
    proof.steps.collect {
      case Step( "eq_transitive", _, ts, _, _ ) =>
        require( ts.size >= 3 )
        val transitivityPremises =
          ts.init
            .map { toExpr( _, Some( To ), renaming ) }
            .map {
              case Neg( Eq( t1, t2 ) ) => ( t1, t2 )
              case p                   => throw AletheException( s"Invalid transitivity premise: ${p}" )
            }
            .toSet
        val Eq( start, target ) = toExpr( ts.last, Some( To ), renaming )
        val edges: Set[( Expr, Expr )] = symmetricClosure( transitivityPremises )
        val Some( terms ) = shortestPath[Expr]( start, target, edges, { case ( _, _ ) => 1 } )
        transitivityAxioms( terms.toList )
    }.flatten.toSet
  }

  object transitivityAxioms {
    def apply( ts: List[Expr] ): List[TransitivityInstance] = {
      ts match {
        case t1 :: t2 :: t3 :: tss =>
          TransitivityInstance( t1, t2, t3 ) ::
            transitivityAxioms( t1 :: t3 :: tss )
        case _ => Nil
      }
    }
  }

  case class ReflexivityInstance( t: Expr )

  def reflexivityInstances( proof: AletheProof, renaming: Map[String, Const] ): Set[FormulaInstance] = {
    collectReflexivityInstances( proof )( renaming ) map {
      case ReflexivityInstance( t ) =>
        FormulaInstance( EqualityReflexivity.formula( t.ty ), Seq( t ) )
    }
  }

  def collectReflexivityInstances( proof: AletheProof )( renaming: Map[String, Const] ): Set[ReflexivityInstance] = {
    proof.steps.collect {
      case Step( "eq_simplify", _, f :: Nil, _, _ ) =>
        toExpr( f, Some( To ), renaming ) match {
          case Iff( Eq( t1, _ ), Top() ) =>
            List( ReflexivityInstance( t1 ) )
          case _ => Nil
        }
      case Step( "eq_reflexive", _, f :: Nil, _, _ ) =>
        val Application( "=", t :: _ ) = f
        List( ReflexivityInstance( toExpr( t, None, renaming ) ) )
    }.flatten.toSet
  }
}

object alethe {

  object toExpr {

    /**
     * Converts an Alethe term to a GAPT expression.
     *
     * @param term The term to be converted
     * @param exptype The expected type of the resulting expression
     * @param constants The GAPT constants to use for the Alethe identifiers.
     */
    def apply( term: Term, exptype: Option[Ty], constants: Map[String, Const] ): Expr = {
      def convertToExpr( term: Term, exptype: Option[Ty], bindings: Map[String, Term] ): Expr = {
        term match {
          case Identifier( name, _ ) =>
            bindings.get( name ).map( convertToExpr( _, exptype, bindings ) ).getOrElse {
              constants.getOrElse( name, Const( name, exptype.getOrElse( Ti ) ) )
            }
          case Application( "not", t :: Nil ) =>
            if ( exptype.isDefined && exptype.get != To ) {
              throw AletheException( s"Expected type ${exptype.get} but got ${To} in '${term}'" )
            }
            Neg( convertToExpr( t, Some( To ), bindings ) )
          case Application( "=", t1 :: t2 :: Nil ) =>
            if ( exptype.isDefined && exptype.get != To ) {
              throw AletheException( s"Expected type ${exptype.get} but got ${To} in '${term}'" )
            }
            val t1_ = convertToExpr( t1, None, bindings )
            val t2_ = convertToExpr( t2, None, bindings )
            ( t1_.ty, t2_.ty ) match {
              case ( To, To ) => Iff( t1_, t2_ )
              case _          => Eq( t1_, t2_ )
            }
          case Application( "or", ts ) =>
            if ( exptype.isDefined && exptype.get != To ) {
              throw AletheException( s"Expected type ${exptype.get} but got ${To} in '${term}'" )
            }
            Or.nAry( ts.map {
              convertToExpr( _, Some( To ), bindings )
            }: _* )
          case Application( "and", ts ) =>
            if ( exptype.isDefined && exptype.get != To ) {
              throw AletheException( s"Expected type ${exptype.get} but got ${To} in '${term}'" )
            }
            And.nAry( ts.map {
              convertToExpr( _, Some( To ), bindings )
            }: _* )
          case Application( "distinct", t1 :: t2 :: t3 :: Nil ) =>
            if ( exptype.isDefined && exptype.get != To ) {
              throw AletheException( s"Expected type ${exptype.get} but got ${To} in '${term}'" )
            }
            val t1_ = convertToExpr( t1, None, bindings )
            val t2_ = convertToExpr( t2, None, bindings )
            val t3_ = convertToExpr( t3, None, bindings )
            And.nAry( Neg( Eq( t1_, t2_ ) ), Neg( Eq( t1_, t3_ ) ), Neg( Eq( t2_, t3_ ) ) )
          case Application( f, as ) =>
            val as_ = as.map {
              convertToExpr( _, None, bindings )
            }
            constants.getOrElse( f, Const( f, FunctionType( exptype.getOrElse( Ti ), as_.map {
              _.ty
            } ) ) )( as_ )
          case True         => Top()
          case False        => Bottom()
          case Let( bs, t ) => convertToExpr( t, exptype, bindings ++ bs )
          case _            => throw AletheException( s"Unsupported term $term" )
        }
      }
      convertToExpr( term, exptype, Map() )
    }
  }
}
