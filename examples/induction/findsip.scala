package at.logic.gapt.examples.induction
import at.logic.gapt.examples.{ Script, UniformAssociativity3ExampleProof }
import at.logic.gapt.expr.FOLTerm
import at.logic.gapt.expr.hol.{ toNNF, simplify, lcomp }
import at.logic.gapt.grammars.{ minimizeSipGrammar, SipGrammarMinimizationFormula, stableSipGrammar }
import at.logic.gapt.proofs.expansion.{ FOLInstanceTermEncoding, toShallow, ExpansionSequent }
import at.logic.gapt.proofs.{ Suc, Ant, HOLSequent }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.maxsat.bestAvailableMaxSatSolver
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.time

object findsip extends Script {
  def removeEqAxioms( eseq: ExpansionSequent ) =
    eseq.zipWithIndex filter {
      case ( et, Ant( _ ) ) => !Prover9.isValid( toShallow( et ) )
      case ( et, Suc( _ ) ) => !Prover9.isValid( -toShallow( et ) )
    } map { _._1 }

  val N = 5
  var instanceSequents = ( 1 until N ) map { n =>
    val instanceProof = UniformAssociativity3ExampleProof( n )
    //  val instanceProof = LinearEqExampleProof(n)
    //  val instanceProof = FactorialFunctionEqualityExampleProof(n)
    n -> removeEqAxioms( LKToExpansionProof( instanceProof ).expansionSequent )
  }

  val endSequent = HOLSequent(
    instanceSequents.flatMap { case ( n, seq ) => toShallow( seq ).antecedent }.distinct,
    Seq( parseFormula( "(x + x) + x = x + (x + x)" ) )
  )
  println( s"End-sequent of the sip: $endSequent" )

  val nLine = sys.props( "line.separator" )

  val encoding = FOLInstanceTermEncoding( endSequent )
  var instanceLanguages = instanceSequents.map {
    case ( n, seq ) =>
      n -> encoding.encode( seq ).map( _.asInstanceOf[FOLTerm] )
  }
  // patch up missing case for n=0
  instanceLanguages = instanceLanguages ++
    Seq( 0 -> Set( encoding.encode( -parseFormula( "0+0=0" ) ).asInstanceOf[FOLTerm] ) )
  instanceLanguages foreach {
    case ( n, l ) =>
      println( s"Instance language for n=$n:$nLine${l.mkString( nLine )}" + nLine )
  }

  println( s"Covering grammar consisting of all normal forms:" )
  val nfGrammar = time {
    stableSipGrammar( instanceLanguages )
  }
  //println(nfGrammar)
  println( s"${nfGrammar.productions.size} productions." )

  val logicalComp = lcomp( simplify( toNNF( SipGrammarMinimizationFormula( nfGrammar ).coversLanguageFamily( instanceLanguages ) ) ) )
  println( s"Logical complexity of the minimization formula: $logicalComp" )

  println( s"Minimized grammar:" )
  val minGrammar = time {
    minimizeSipGrammar( nfGrammar, instanceLanguages, maxSATSolver = bestAvailableMaxSatSolver )
  }
  println( minGrammar )
  println()

  instanceLanguages foreach {
    case ( n, instanceLanguage ) =>
      val instanceGrammar = minGrammar.instanceGrammar( n )
      println( s"Instance language for n=$n covered? " + ( instanceLanguage.toSet diff instanceGrammar.language ).isEmpty )
    //  println(s"Instance grammar:" + nLine + "$instanceGrammar")
  }
}
