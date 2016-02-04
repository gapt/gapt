package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution._

object resolutionToTptp {
  def fofOrCnf( label: String, role: FormulaRole, inf: ResolutionProof, annotations: Seq[GeneralTerm] ): TptpInput = {
    val disj = if ( inf.assertions.isEmpty ) inf.conclusion.toDisjunction
    else inf.conclusion.toDisjunction | inf.assertions.toDisjunction
    if ( inf.conclusion.forall( _.isInstanceOf[HOLAtom] ) ) {
      val ( _, disj_ ) = tptpToString.renameVars( freeVariables( disj ).toSeq, disj )
      AnnotatedFormula( "cnf", label, role, disj_.asInstanceOf[HOLFormula], annotations )
    } else {
      AnnotatedFormula( "fof", label, role, disj, annotations )
    }
  }

  def convertDefinition(
    label:    String,
    defConst: HOLAtomConst,
    defn:     LambdaExpression
  ): TptpInput = {
    val FunctionType( _, argtypes ) = defConst.exptype
    val vars = for ( ( t, i ) <- argtypes.zipWithIndex ) yield Var( s"X$i", t )

    AnnotatedFormula( "fof", label, "definition",
      BetaReduction.betaNormalize( All.Block( vars, defConst( vars: _* ) <-> defn( vars: _* ) ) ),
      Seq() )
  }

  def convertInference(
    labelMap: Map[ResolutionProof, String],
    defMap:   Map[HOLAtomConst, String],
    inf:      ResolutionProof
  ): TptpInput = {
    val label = labelMap( inf )
    inf match {
      case Input( sequent ) =>
        fofOrCnf( label, "axiom", inf, Seq() )

      case p =>
        val inferenceName = p.longName.flatMap {
          case c if c.isUpper => "_" + c.toLower
          case c              => c.toString
        }.dropWhile( _ == '_' )

        val parents = p.immediateSubProofs.map( labelMap ) ++ p.introducedDefinitions.keys.map( defMap )

        fofOrCnf( label, "plain", inf,
          Seq( TptpTerm( "inference", FOLConst( inferenceName ),
            GeneralList(), GeneralList( parents.map( FOLConst( _ ) ) ) ) ) )
    }
  }

  def apply( proof: ResolutionProof ): Seq[TptpInput] = {
    val defMap = ( for ( ( dc, i ) <- proof.definitions.keys.zipWithIndex ) yield dc -> s"def$i" ).toMap
    val labelMap = ( for ( ( p, i ) <- proof.dagLike.postOrder.zipWithIndex ) yield p -> s"p$i" ).toMap
    proof.definitions.toSeq.map { case ( dc, dn ) => convertDefinition( defMap( dc ), dc, dn ) } ++
      proof.dagLike.postOrder.map { convertInference( labelMap, defMap, _ ) }
  }
}
