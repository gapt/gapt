package gapt.formats.tptp

import gapt.expr._
import gapt.expr.hol.{ instantiate, universalClosure }
import gapt.proofs.resolution._

import scala.collection.mutable

object resolutionToTptp {
  def fofOrCnf( label: String, role: FormulaRole, inf: ResolutionProof, annotations: Seq[GeneralTerm] ): TptpInput = {
    val disj = if ( inf.assertions.isEmpty ) inf.conclusion.toDisjunction
    else inf.conclusion.toDisjunction | inf.assertions.toDisjunction
    if ( inf.conclusion.forall( _.isInstanceOf[Atom] ) ) {
      AnnotatedFormula( "cnf", label, role, TptpToString.renameVars( disj ), annotations )
    } else {
      AnnotatedFormula( "fof", label, role, universalClosure( disj ), annotations )
    }
  }

  private def convertDefinition(
    label:    String,
    defConst: HOLAtomConst,
    defn:     Expr ): TptpInput = {
    val FunctionType( _, argtypes ) = defConst.ty
    val vars = for ( ( t, i ) <- argtypes.zipWithIndex ) yield Var( s"X$i", t )

    AnnotatedFormula( "fof", label, "definition",
      BetaReduction.betaNormalize( All.Block( vars, defConst( vars: _* ) <-> defn( vars: _* ) ) ),
      Seq() )
  }

  private def convertSkolemDefinition(
    label:   String,
    skConst: Const,
    defn:    Expr ): AnnotatedFormula = {
    val Abs.Block( vars, quantf: Formula ) = defn
    val instf = instantiate( quantf, skConst( vars ) )

    AnnotatedFormula( "fof", label, "definition",
      All.Block( vars, quantf match {
        case Ex( _, _ )  => quantf --> instf
        case All( _, _ ) => instf --> quantf
      } ),
      Seq() )
  }

  private def convertInference(
    labelMap: collection.Map[ResolutionProof, String],
    defMap:   collection.Map[Const, String],
    inf:      ResolutionProof ): TptpInput = {
    val label = labelMap( inf )
    inf match {
      case Input( sequent ) =>
        fofOrCnf( label, "axiom", inf, Seq() )

      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile( _ == '_' )

        val parents = p.immediateSubProofs.map( labelMap ) ++
          p.introducedDefinitions.keys.map( defMap ) ++
          Some( p ).collect { case p: SkolemQuantResolutionRule => defMap( p.skolemConst ) }

        fofOrCnf( label, "plain", inf,
          Seq( TptpTerm( "inference", FOLConst( inferenceName ),
            GeneralList(), GeneralList( parents.map( FOLConst( _ ) ) ) ) ) )
    }
  }

  def apply( proof: ResolutionProof ): TptpFile = {
    val inputs = Seq.newBuilder[TptpInput]

    val defMap = mutable.Map[Const, String]()
    for ( ( ( dc, defn ), i ) <- proof.definitions.toSeq.zipWithIndex ) {
      defMap( dc ) = s"def$i"
      inputs += convertDefinition( defMap( dc ), dc, defn )
    }

    val skFuns = proof.skolemFunctions
    for ( ( dc, i ) <- skFuns.dependencyOrder.zipWithIndex ) {
      defMap( dc ) = s"skdef$i"
      inputs += convertSkolemDefinition( defMap( dc ), dc, skFuns.skolemDefs( dc ) )
    }

    val labelMap = mutable.Map[ResolutionProof, String]()
    for ( ( p, i ) <- proof.dagLike.postOrder.zipWithIndex ) {
      labelMap( p ) = s"p$i"
      inputs += convertInference( labelMap, defMap, p )
    }

    TptpFile( inputs.result() )
  }
}
