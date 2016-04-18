package at.logic.gapt.examples.recschem
import at.logic.gapt.examples.{ Script, UniformAssociativity3ExampleProof }
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.expr._
import at.logic.gapt.grammars.{ SipRecSchem, minimizeRecursionScheme, minimizeSipGrammar, stableSipGrammar }
import at.logic.gapt.proofs.expansion.{ ExpansionSequent, FOLInstanceTermEncoding }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.proofs.{ Ant, Sequent, Suc }
import at.logic.gapt.provers.maxsat.bestAvailableMaxSatSolver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.utils.time

object sip_comparison extends Script {

  def removeEqAxioms( eseq: ExpansionSequent ) =
    eseq.zipWithIndex filter {
      case ( et, Ant( _ ) ) => !Escargot.isValid( et.shallow )
      case ( et, Suc( _ ) ) => !Escargot.isValid( -et.shallow )
    } map { _._1 }

  val endSequent = fof"∀x ∀y s(x+y) = x+s(y)" +: fof"∀x x+0 = x" +:
    Sequent() :+ fof"(x+x)+x = x+(x+x)"
  val instanceProofs =
    ( 0 until 6 ).map { n => n -> removeEqAxioms( LKToExpansionProof( UniformAssociativity3ExampleProof( n ) ).expansionSequent ) }

  val termEncoding = FOLInstanceTermEncoding( endSequent )
  var instanceLanguages = instanceProofs map {
    case ( n, expSeq ) =>
      n -> termEncoding.encode( expSeq ).map( _.asInstanceOf[FOLTerm] )
  }

  // Ground the instance languages.
  instanceLanguages = instanceLanguages map {
    case ( n, lang ) =>
      val groundingSubst = FOLSubstitution( freeVariables( lang ).
        map { c => FOLVar( c.name ) -> FOLConst( c.name ) }.toSeq )
      n -> lang.map( groundingSubst( _ ) )
  }

  val nfRecSchem = SipRecSchem.stableRecSchem( instanceLanguages )
  println( nfRecSchem.rules.size )
  println( "Recursion scheme minimization:" )
  val minimized = time {
    minimizeRecursionScheme( nfRecSchem, SipRecSchem.toTargets( instanceLanguages ), SipRecSchem.targetFilter, bestAvailableMaxSatSolver )
  }
  println( minimized )
  println

  println( "Recursion scheme minimization via instantiation:" )
  val minimizedInst = time {
    minimizeRecursionScheme.viaInst( nfRecSchem, SipRecSchem.toTargets( instanceLanguages ), SipRecSchem.targetFilter, bestAvailableMaxSatSolver )
  }
  println( minimizedInst )
  println

  ( 0 until 10 ) foreach { i =>
    val instanceLang = minimized.parametricLanguage( Numeral( i ) )
    val instanceSeq = FOLSubstitution( FOLVar( "x" ) -> Numeral( i ) )( termEncoding decodeToInstanceSequent instanceLang )
    val isCovered = instanceLanguages.find( _._1 == i ).map( _._2.toSet subsetOf instanceLang )
    val isTaut = VeriT.isValid( instanceSeq )
    println( s"$i: tautology=$isTaut covers=$isCovered" )
  }

  val sipG = SipRecSchem.toSipGrammar( minimized )
  println( sipG )

  val nfSipG = stableSipGrammar( instanceLanguages )
  println( nfSipG.productions.size )
  println( time { minimizeSipGrammar( nfSipG, instanceLanguages, bestAvailableMaxSatSolver ) } )
}
