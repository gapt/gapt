package at.logic.gapt.formats.tptp

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFn, CNFp, univclosure }
import at.logic.gapt.proofs.resolution.{ AvatarComponent, AvatarGroundComp, AvatarNonGroundComp }
import at.logic.gapt.proofs.sketch._
import at.logic.gapt.proofs.{ FOLClause, HOLClause, Sequent }

import scala.collection.mutable

object TptpProofParser {
  def parse( out: String, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch =
    parseSteps( TptpParser.parseString( out ), labelledCNF )

  def parse( out: String ): ( Sequent[FOLFormula], RefutationSketch ) = {
    val tptpFile_ = TptpParser.parseString( out )
    val tptpFile = inventSources( tptpFile_ )
    val ( endSequent, labelledCNF ) = extractEndSequentAndCNF( tptpFile )
    endSequent -> parseSteps( tptpFile, labelledCNF )
  }

  def inventSources( stepList: TptpFile ): TptpFile = TptpFile( stepList.inputs map {
    case af @ AnnotatedFormula( lang, label, role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula, Seq() ) =>
      af.copy( annotations = Seq( TptpTerm( "file", TptpTerm( "unknown" ), TptpTerm( s"source_$label" ) ) ) )
    case af @ AnnotatedFormula( lang, label, role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula,
      Seq( TptpTerm( "file", _, TptpTerm( "unknown" ) ), _* ) ) =>
      af.copy( annotations = Seq( TptpTerm( "file", TptpTerm( "unknown" ), TptpTerm( s"source_$label" ) ) ) )
    case other => other
  } )

  def extractEndSequentAndCNF( stepList: TptpFile ): ( Sequent[FOLFormula], Map[String, Seq[FOLClause]] ) = {
    var endSequent = Sequent[FOLFormula]()
    var labelledCNF = Map[String, Seq[FOLClause]]()

    stepList.inputs foreach {
      case AnnotatedFormula( "fof", _, "conjecture", formula: FOLFormula, Seq( TptpTerm( "file", _, TptpTerm( label ) ) ) ) =>
        endSequent :+= formula
        labelledCNF += label -> CNFn.toClauseList( formula )
      case AnnotatedFormula( lang, _, _, formula: FOLFormula, Seq( TptpTerm( "file", _, TptpTerm( label ) ) ) ) =>
        endSequent +:= ( if ( lang == "cnf" ) univclosure( formula ) else formula )
        labelledCNF += label -> CNFp.toClauseList( formula )
      case _ =>
    }

    endSequent -> labelledCNF
  }

  def parseSteps( stepList: TptpFile, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch = {
    val steps = ( for ( input @ AnnotatedFormula( _, name, _, _, _ ) <- stepList.inputs ) yield name -> input ).toMap

    def getParents( justification: GeneralTerm ): Seq[String] = justification match {
      case TptpTerm( "inference", _, _, GeneralList( parents @ _* ) ) => parents flatMap getParents
      case TptpTerm( "introduced", _, _ )                             => Seq()
      case TptpTerm( "theory", TptpTerm( "equality", _* ), _* )       => Seq()
      case GeneralColon( TptpTerm( label ), _ )                       => Seq( label )
      case TptpTerm( dagSource )                                      => Seq( dagSource )
    }

    val memo = mutable.Map[String, Seq[RefutationSketch]]()
    val splDefs = mutable.Map[( FOLAtom, Boolean ), AvatarComponent]()
    val splAtoms = mutable.Set[FOLAtom]()
    def filterVampireSplits( clause: FOLClause ): FOLClause = clause.filterNot( splAtoms )
    def convertAvatarDefinition( defn: HOLFormula, splAtom: FOLAtom ): Seq[RefutationSketch] = {
      val All.Block( vs, clauseDisj ) = defn
      splAtoms += splAtom
      val comps = defn match {
        case splAtom @ FOLAtom( _, _ ) if freeVariables( splAtom ).isEmpty =>
          Seq( false, true ) map { AvatarGroundComp( splAtom, _ ) }
        case Neg( splAtom @ FOLAtom( _, _ ) ) if freeVariables( splAtom ).isEmpty =>
          Seq( false, true ) map { AvatarGroundComp( splAtom, _ ) }
        case _ =>
          Seq( AvatarNonGroundComp( splAtom, AvatarNonGroundComp.DefinitionFormula.canonize( defn ) ) )
      }
      comps map { comp =>
        splDefs( ( splAtom, comp.assertion.succedent.nonEmpty ) ) = comp
        SketchComponentIntro( comp )
      }
    }
    def convert( stepName: String ): Seq[RefutationSketch] = memo.getOrElseUpdate( stepName, steps( stepName ) match {
      case AnnotatedFormula( "fof", _, "plain", And( Imp( defn, Neg( splAtom: FOLAtom ) ), _ ), TptpTerm( "introduced", TptpTerm( "sat_splitting_component" ), _ ) +: _ ) =>
        convertAvatarDefinition( defn, splAtom )
      case AnnotatedFormula( "fof", _, "plain", Bottom(), ( justification @ TptpTerm( "inference", TptpTerm( "sat_splitting_refutation" ), _, _ ) ) +: _ ) =>
        val sketchParents = getParents( justification ) flatMap convert
        val splitParents = sketchParents map { parent0 =>
          var parent = parent0
          while ( parent.conclusion.nonEmpty ) {
            val ( comp, subst ) = splDefs.values.view.
              flatMap { d => clauseSubsumption( d.clause, parent.conclusion ) filter { _.isInjectiveRenaming } map { d -> _ } }.
              headOption.getOrElse {
                throw new IllegalArgumentException( parent.conclusion.toString )
              }
            parent = SketchComponentElim( parent, comp match {
              case AvatarNonGroundComp( splAtom, defn, vars ) =>
                AvatarNonGroundComp( splAtom, defn, subst( vars ).map( _.asInstanceOf[Var] ) )
              case AvatarGroundComp( _, _ ) => comp
            } )
          }
          parent
        }
        Seq( SketchSplitCombine( splitParents ) )
      case AnnotatedFormula( "fof", _, "plain", And( Imp( splAtom: FOLAtom, defn ), _ ), TptpTerm( "introduced", FOLVar( "AVATAR_definition" ), _ ) +: _ ) =>
        convertAvatarDefinition( defn, splAtom )
      case AnnotatedFormula( "fof", _, "plain", disj, ( justification @ TptpTerm( "inference", FOLVar( "AVATAR_split_clause" ), _, _ ) ) +: _ ) =>
        val Seq( assertion ) = CNFp.toClauseList( disj )
        val Seq( splittedClause, _* ) = getParents( justification ) flatMap convert

        var p = splittedClause
        for {
          ( splAtom: FOLAtom, i ) <- assertion.zipWithIndex
          comp <- splDefs.get( ( splAtom, i.isSuc ) )
          subst <- clauseSubsumption( comp.clause, p.conclusion )
        } p = SketchComponentElim( p, comp match {
          case comp @ AvatarNonGroundComp( _, _, vars ) =>
            comp.copy( vars = subst( vars ).map( _.asInstanceOf[Var] ) )
          case AvatarGroundComp( _, _ ) => comp
        } )

        require( p.conclusion.isEmpty, s"$assertion\n$splittedClause\n$splDefs" )
        Seq( p )
      case AnnotatedFormula( "fof", _, "plain", Bottom(), ( justification @ TptpTerm( "inference", FOLVar( "AVATAR_sat_refutation" ), _, _ ) ) +: _ ) =>
        Seq( SketchSplitCombine( getParents( justification ).flatMap( convert ) ) )
      case AnnotatedFormula( "fof", _, "conjecture", _, TptpTerm( "file", _, TptpTerm( label ) ) +: _ ) =>
        labelledCNF( label ) map SketchAxiom
      case AnnotatedFormula( _, _, _, axiom: FOLFormula, TptpTerm( "file", _, TptpTerm( label ) ) +: _ ) =>
        CNFp.toClauseList( axiom ) match {
          case Seq( axiomClause ) =>
            Seq( SketchInference(
              axiomClause,
              labelledCNF( label ) map SketchAxiom
            ) )
          case clauses => labelledCNF( label ) map SketchAxiom
        }
      case AnnotatedFormula( "cnf", _, "axiom", axiom: FOLFormula, Seq() ) =>
        val label = stepName
        CNFp.toClauseList( axiom ) match {
          case Seq( axiomClause ) =>
            Seq( SketchInference(
              axiomClause,
              labelledCNF( label ) map SketchAxiom
            ) )
          case clauses => labelledCNF( label ) map SketchAxiom
        }
      case AnnotatedFormula( _, _, _, conclusion: FOLFormula, justification +: _ ) =>
        CNFp.toClauseList( conclusion ) match {
          case Seq( conclusionClause ) =>
            val sketchParents = getParents( justification ) flatMap convert
            val conclusionClause_ = filterVampireSplits( conclusionClause )
            val sketchParents_ = sketchParents.
              find( p => clauseSubsumption( p.conclusion, conclusionClause_ ).isDefined ).
              fold( sketchParents )( Seq( _ ) )
            Seq( SketchInference( conclusionClause_, sketchParents_ ) )
          case clauses => getParents( justification ) flatMap convert
        }
    } )

    val emptyClauseLabel = stepList.inputs.collect { case AnnotatedFormula( _, label, _, Bottom(), _ ) => label }.head
    convert( emptyClauseLabel ).head

  }
}
