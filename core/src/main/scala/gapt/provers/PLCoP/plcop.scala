package gapt.provers.PLcop

import java.io.IOException
import java.io.StringReader
import gapt.expr.formula.hol.universalClosure
import gapt.expr.formula.{ All, Atom, Eq, Neg, Or }
import gapt.expr.subst.Substitution
import gapt.formats.PLCop.{ PLCopParser }
import gapt.proofs.expansion.{ ETWeakQuantifierBlock, ExpansionProof, ExpansionProofToLK, ExpansionSequent, formulaToExpansionTree }
import gapt.formats.tptp.TptpFOLExporter
import gapt.logic.{ Polarity, clauseSubsumption }
import gapt.proofs.{ Clause, HOLClause, HOLSequent, Sequent }
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionToExpansionProof
import gapt.proofs.resolution.expansionProofFromInstances
import gapt.proofs.resolution.structuralCNF
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.OneShotProver
import gapt.provers.renameConstantsToFi
import gapt.utils.EitherHelpers._
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess
import gapt.utils.withTempFile
import java.io.File
import gapt.formats.InputFile
import gapt.proofs.expansion.deskolemizeET
trait AltProver extends OneShotProver { self =>
  def extendToManySortedViaPredicates = new OneShotProver {
    import gapt.proofs.reduction._
    override def isValid( sequent: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean = {
      val reduction = PredicateReductionET |> ErasureReductionET
      val ( folProblem, _ ) = reduction forward sequent
      self.getExpansionProof( folProblem )( ctx.map( _.newMutable ) ).isDefined
    }

    override def getExpansionProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
      val reduction = PredicateReductionET |> ErasureReductionET
      val ( folProblem, back ) = reduction forward sequent
      print( folProblem.toString + "\n" )
      //error occur because expansionproof in PLCOP call clause transformations have.
      //have to break the function apart....
      self.getExpansionProof( folProblem ).map( exp => {
        print( exp.toString + "\n" )
        back( deskolemizeET( exp ) )
      } )
    }

    override def getLKProof( sequent: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
      val reduction = PredicateReductionET |> ErasureReductionET
      val ( folProblem, back ) = reduction forward sequent
      getExpansionProof( folProblem ) map { ExpansionProofToLK( _ ).get }
    }
    override def toString = s"$self.extendToManySortedViaPredicates"
  }
}
object PLCop extends PLCop( ini = "ini/plcop0.ini", stage = "0", exeDic = "./leancop_ml" )
class PLCop( ini: String = "ini/plcop0.ini", stage: String = "0", exeDic: String = "./leancop_ml" ) extends AltProver with ExternalProgram {
  //private val exeDic = "/home/cernadavid1/SVN_REPOS/leancop_ml"
  override def isValid( s: HOLSequent )( implicit ctx: Maybe[Context] ): Boolean =
    getExpansionProof( s )( ctx.map( _.newMutable ) ).isDefined

  override def getExpansionProof( s: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] = {
    val cnf = structuralCNF( s ).map( c => universalClosure( c.conclusion.toDisjunction ) -> c ).toMap
    // LeanCoP doesn't like empty clauses
    for ( ( _, clause ) <- cnf if clause.isProof ) return Some( ResolutionToExpansionProof( clause ) )
    renameConstantsToFi.wrap( cnf.keys ++: Sequent() )( ( renaming, sequent: HOLSequent ) => {
      val tptp = TptpFOLExporter( sequent ).toString
      val ( exitValue, stdout ) = withTempFile.fromString( tptp ) { leanCoPInput =>
        runProcess.withExitValue( Seq( "python", "montecarlo.py", ini, "--stage", stage, "--problem_file", leanCoPInput.toIO.getAbsolutePath(), "--outdir", "/tmp" ), exeDict = exeDic )
        val outputFile = "/tmp" + "/" + "stage" + stage + "/proofs" + leanCoPInput.toIO.getAbsolutePath()
        if ( new File( outputFile ).exists() ) ( 0, outputFile ) else ( 1, "" )
      }
      if ( exitValue == 1 ) None
      else if ( exitValue == 0 ) Some( PLCopParser.getExpansionProof( InputFile.fromFileName( stdout ) ).get )
      else throw new IllegalArgumentException( s"Unexpected PLCop output with exit value ${exitValue}:\n${stdout}" )

    } ).map {
      case es =>
        val hasEquality = cnf.values.flatMap( _.conclusion.elements ).exists {
          case Eq( _, _ ) => true
          case _          => false
        }
        val substs = for {
          ETWeakQuantifierBlock( shallow, _, insts ) <- es.elements
          ( formula @ All.Block( vars, _ ), clause ) <- cnf
          if formula == shallow
        } yield clause.conclusion.asInstanceOf[HOLClause] ->
          insts.keys.map( s => Substitution( vars zip s ) ).toSet
        expansionProofFromInstances( substs.toMap, cnf.values.toSet, !hasEquality )
    }
  }

  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    getExpansionProof( seq ) map { ExpansionProofToLK( _ ).get }

  override val isInstalled: Boolean = try runProcess.withExitValue( Seq( "leancop" ) )._1 == 2
  catch { case _: IOException => false }
}
