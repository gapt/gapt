package gapt.formats.tptp

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.FOLAtom
import gapt.expr.formula.FOLConst
import gapt.expr.formula.FOLFormula
import gapt.expr.formula.FOLVar
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.hol.{ containsStrongQuantifier, universalClosure }
import gapt.expr.util.clauseSubsumption
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.logic.Polarity
import gapt.logic.hol.CNFn
import gapt.logic.hol.CNFp
import gapt.proofs.resolution.{ AvatarDefinition, AvatarGroundComp, AvatarNonGroundComp, AvatarSplit }
import gapt.proofs.sketch._
import gapt.proofs.{ FOLClause, HOLClause, HOLSequent, Sequent }

import scala.collection.mutable

/**
 * Represents a malformed input file e.g. one that contains an unknown parent step
 */
class MalformedInputFileException( s: String ) extends IllegalArgumentException( s )

object TptpProofParser {
  def parse( out: InputFile, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch =
    parseSteps( TptpImporter.loadWithoutIncludes( out ), labelledCNF )

  def removeStrongQuants( tptpFile: TptpFile ): TptpFile = {
    val stepsWithStrongQuants = tptpFile.inputs.filter {
      case AnnotatedFormula( _, _, _, _, TptpTerm( "introduced", TptpTerm( sat_splitting ), _ ) +: _
        ) if sat_splitting.startsWith( "sat_splitting" ) =>
        false
      case AnnotatedFormula( _, _, _, _, TptpTerm( "introduced", FOLVar( avatar ), _ ) +: _
        ) if avatar.startsWith( "AVATAR" ) =>
        false
      case AnnotatedFormula( _, _, _, _, TptpTerm( "introduced", FOLConst( avatar ), _ ) +: _
        ) if avatar.startsWith( "avatar" ) =>
        false
      case AnnotatedFormula( _, label, "conjecture", formula, _ ) =>
        containsStrongQuantifier( formula, Polarity.InSuccedent )
      case AnnotatedFormula( _, label, _, formula, _ ) =>
        containsStrongQuantifier( formula, Polarity.InAntecedent )
      case _ => false
    }.collect { case f: AnnotatedFormula => f.name }.toSet
    if ( stepsWithStrongQuants.isEmpty )
      tptpFile
    else
      TptpFile( tptpFile.inputs.collect { case f: AnnotatedFormula if !stepsWithStrongQuants( f.name ) => f }.map {
        case f @ AnnotatedFormula( _, _, _, _, just +: _ ) if getParents( just ).
          toSet.intersect( stepsWithStrongQuants ).isEmpty => f
        case f @ AnnotatedFormula( _, label, "conjecture", formula, _ ) =>
          AnnotatedFormula( "fof", label, "conjecture", formula, Seq() )
        case f => AnnotatedFormula( "fof", f.name, "axiom", f.formula, Seq() )
      } )
  }

  def parse( out: InputFile, ignoreStrongQuants: Boolean = false ): ( Sequent[FOLFormula], RefutationSketch ) = {
    var tptpFile = TptpImporter.loadWithoutIncludes( out )
    if ( ignoreStrongQuants ) tptpFile = removeStrongQuants( tptpFile )
    tptpFile = inventSources( tptpFile )
    val ( endSequent, labelledCNF ) = extractEndSequentAndCNF( tptpFile )
    endSequent -> parseSteps( tptpFile, labelledCNF )
  }

  def inventSources( stepList: TptpFile ): TptpFile = TptpFile( stepList.inputs map {
    case af @ AnnotatedFormula( lang, label,
      role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula, Seq() ) =>
      af.copy( annotations = Seq( TptpTerm( "file", TptpTerm( "unknown" ), TptpTerm( s"source_$label" ) ) ) )
    case af @ AnnotatedFormula( lang, label,
      role @ ( "axiom" | "hypothesis" | "conjecture" | "negated_conjecture" ), formula,
      Seq( TptpTerm( "file", _, TptpTerm( "unknown" ) ), _* ) ) =>
      af.copy( annotations = Seq( TptpTerm( "file", TptpTerm( "unknown" ), TptpTerm( s"source_$label" ) ) ) )
    case other => other
  } )

  def extractEndSequentAndCNF( stepList: TptpFile ): ( Sequent[FOLFormula], Map[String, Seq[FOLClause]] ) = {
    var endSequent = Sequent[FOLFormula]()
    val labelledCNF = mutable.Map[String, Seq[FOLClause]]().withDefaultValue( Seq() )

    stepList.inputs foreach {
      case AnnotatedFormula( "fof", _, "conjecture", formula: FOLFormula,
        Seq( TptpTerm( "file", _, TptpTerm( label ) ) ) ) =>
        endSequent :+= formula
        labelledCNF( label ) ++= CNFn( formula ).toSeq
      case AnnotatedFormula( lang, _, _, formula: FOLFormula, Seq( TptpTerm( "file", _, TptpTerm( label ) ) ) ) =>
        endSequent +:= ( if ( lang == "cnf" ) universalClosure( formula ) else formula )
        labelledCNF( label ) ++= CNFp( formula ).toSeq
      case _ =>
    }

    endSequent -> labelledCNF.toMap
  }

  def getParents( justification: GeneralTerm ): Seq[String] = justification match {
    case TptpTerm( "file", _, _ )                                   => Seq()
    case TptpTerm( "inference", _, _, GeneralList( parents @ _* ) ) => parents flatMap getParents
    case TptpTerm( "introduced", _, _ )                             => Seq()
    case TptpTerm( "theory", TptpTerm( "equality", _* ), _* )       => Seq()
    case GeneralColon( TptpTerm( label ), _ )                       => Seq( label )
    case TptpTerm( dagSource )                                      => Seq( dagSource )
  }

  def findClauseRenaming( from: HOLSequent, to: HOLSequent ): Option[Map[Var, Var]] =
    if ( from.sizes != to.sizes )
      None
    else for {
      subst <- clauseSubsumption( from, to )
      // FIXME: this would only be correct if we considered all subsumptions...
      if subst.isInjectiveRenaming
    } yield subst.map.map { case ( l, r ) => l -> r.asInstanceOf[Var] }

  def parseSteps( stepList: TptpFile, labelledCNF: Map[String, Seq[FOLClause]] ): RefutationSketch = {
    val steps = ( for ( input @ AnnotatedFormula( _, name, _, _, _ ) <- stepList.inputs )
      yield name -> input ).toMap

    val memo = mutable.Map[String, Seq[RefutationSketch]]()
    val alreadyVisited = mutable.Set[String]()
    val splDefs = mutable.Map[( FOLAtom, Boolean ), AvatarDefinition]()
    val splAtoms = mutable.Set[FOLAtom]()

    def filterVampireSplits( clause: FOLClause ): FOLClause = clause.filterNot( splAtoms )

    def convertAvatarDefinition( defn: Formula, splAtom: FOLAtom ): Seq[RefutationSketch] = {
      splAtoms += splAtom
      val comps = defn match {
        case splAtom @ FOLAtom( _, _ ) if freeVariables( splAtom ).isEmpty =>
          Polarity.values.map {
            AvatarGroundComp( splAtom, _ )
          }
        case Neg( splAtom @ FOLAtom( _, _ ) ) if freeVariables( splAtom ).isEmpty =>
          Polarity.values.map {
            AvatarGroundComp( splAtom, _ )
          }
        case _ =>
          Seq( AvatarNonGroundComp( splAtom, AvatarNonGroundComp.DefinitionFormula.canonize( defn ) ) )
      }
      comps map { comp =>
        splDefs( ( splAtom, comp.assertion.succedent.nonEmpty ) ) = comp
        SketchComponentIntro( comp )
      }
    }

    def haveAlreadyVisited( stepName: String ): Boolean = {
      val res = alreadyVisited( stepName )
      alreadyVisited += stepName
      res
    }

    def convert( stepName: String ): Seq[RefutationSketch] = {
      val step = steps.getOrElse( stepName, throw new MalformedInputFileException( s"unknown step $stepName" ) )

      memo.getOrElseUpdate( stepName, step match {
        case _ if haveAlreadyVisited( stepName ) =>
          throw new IllegalArgumentException( s"Cyclic inference: ${steps( stepName )}" )
        case AnnotatedFormula( "fof", _, "plain", And( Imp( defn, Neg( splAtom: FOLAtom ) ), _ ),
          TptpTerm( "introduced", TptpTerm( "sat_splitting_component" ), _ ) +: _ ) =>
          convertAvatarDefinition( defn, splAtom )
        case AnnotatedFormula( "fof", _, "plain", Bottom(),
          ( justification @ TptpTerm( "inference", TptpTerm( "sat_splitting_refutation" ),
            _, _ ) ) +: _ ) =>
          val sketchParents = getParents( justification ) flatMap convert
          val splitParents = sketchParents map { parent0 =>
            var parent = parent0
            for {
              clauseComponent <- AvatarSplit.getComponents( parent0.conclusion )
              comp <- splDefs.values
              renaming <- findClauseRenaming( comp.clause, clauseComponent )
            } parent = SketchComponentElim( parent, comp match {
              case comp @ AvatarNonGroundComp( _, _, vars ) => comp.copy( vars = vars.map( renaming ) )
              case AvatarGroundComp( _, _ )                 => comp
            } )
            require( parent.conclusion.isEmpty )
            parent
          }
          Seq( SketchSplitCombine( splitParents ) )
        case AnnotatedFormula( "fof", _, "plain", And( Imp( splAtom: FOLAtom, defn ), _ ),
          TptpTerm( "introduced", FOLVar( "AVATAR_definition" ) | FOLConst( "avatar_definition" ), _ ) +: _ ) =>
          convertAvatarDefinition( defn, splAtom )
        case AnnotatedFormula( "fof", _, "plain", disj,
          ( justification @ TptpTerm( "inference", FOLVar( "AVATAR_split_clause" ) | FOLConst( "avatar_split_clause" ),
            _, _ ) ) +: _ ) =>
          val Seq( assertion ) = CNFp( disj ).toSeq
          val Seq( splittedClause, _* ) = getParents( justification ) flatMap convert

          var p = splittedClause
          for {
            clauseComponent <- AvatarSplit.getComponents( splittedClause.conclusion )
            ( splAtom: FOLAtom, i ) <- assertion.zipWithIndex
            comp <- splDefs.get( ( splAtom, i.isSuc ) )
            renaming <- findClauseRenaming( comp.clause, clauseComponent )
          } p = SketchComponentElim( p, comp match {
            case comp @ AvatarNonGroundComp( _, _, vars ) => comp.copy( vars = vars.map( renaming ) )
            case AvatarGroundComp( _, _ )                 => comp
          } )

          require( p.conclusion.isEmpty, s"$assertion\n$splittedClause\n$splDefs" )
          Seq( p )
        case AnnotatedFormula( "fof", _, "plain", Bottom(),
          ( justification @ TptpTerm( "inference", FOLVar( "AVATAR_sat_refutation" ) |
            FOLConst( "avatar_sat_refutation" ), _, _ ) ) +: _ ) =>
          Seq( SketchSplitCombine( getParents( justification ).flatMap( convert ) ) )
        case AnnotatedFormula( "fof", _, "conjecture", _, TptpTerm( "file", _, TptpTerm( label ) ) +: _ ) =>
          labelledCNF( label ) map SketchAxiom
        case AnnotatedFormula( _, _, _, axiom: FOLFormula, TptpTerm( "file", _, TptpTerm( label ) ) +: _ ) =>
          CNFp( axiom ).toSeq match {
            case Seq( axiomClause ) =>
              Seq( SketchInference(
                axiomClause,
                labelledCNF( label ) map SketchAxiom ) )
            case clauses => labelledCNF( label ) map SketchAxiom
          }
        case AnnotatedFormula( "cnf", _, "axiom", axiom: FOLFormula, Seq() ) =>
          val label = stepName
          CNFp( axiom ).toSeq match {
            case Seq( axiomClause ) =>
              Seq( SketchInference(
                axiomClause,
                labelledCNF( label ) map SketchAxiom ) )
            case clauses => labelledCNF( label ) map SketchAxiom
          }
        case AnnotatedFormula( _, _, _, conclusion: FOLFormula, justification +: _ ) =>
          CNFp( conclusion ).toSeq match {
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
    }

    val emptyClauseLabel = stepList.inputs.collect {
      case AnnotatedFormula( _, label, _, Bottom(), _ ) => label
    }.head
    convert( emptyClauseLabel ).head

  }
}
