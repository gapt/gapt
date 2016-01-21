package at.logic.gapt.proofs.shlk

import at.logic.gapt.proofs.lkOld.base.{ LKProof, OccSequent }
import at.logic.gapt.proofs.lkOld.{ Axiom, BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.shlk._

object printSchemaProof {
  val nLine = sys.props( "line.separator" )

  // TODO: this should move to where Sequent is declared...
  def sequentToString( s: OccSequent ): String = {
    var sb = new scala.StringBuilder()
    var first = true
    for ( f <- s.antecedent ) {
      if ( !first ) sb.append( ", " )
      else first = false
      sb.append( f.toString )
    }
    sb.append( Console.RED + " \u22a2 " + Console.RESET )
    first = true
    for ( f <- s.succedent ) {
      if ( !first ) sb.append( ", " )
      else first = false
      sb.append( f.formula.toString )
    }
    sb.toString
  }

  def apply( p: LKProof ): Unit = p match {
    case SchemaProofLinkRule( seq, _, _ ) => println( nLine + " SchemaProofLinkRule : " + sequentToString( seq ) )
    case Axiom( seq )                     => println( nLine + " Axiom : " + sequentToString( seq ) )

    case UnaryLKProof( _, up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case BinaryLKProof( _, up1, up2, r, _, _, _ ) => {
      apply( up1 )
      apply( up2 )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }

    case AndEquivalenceRule1( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case AndEquivalenceRule2( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case AndEquivalenceRule3( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case OrEquivalenceRule1( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case OrEquivalenceRule2( up, r, _, _ ) => {
      apply( up )
      println( nLine + " UnaryProof : " + sequentToString( r ) )
    }
    case OrEquivalenceRule3( up, r, _, _ ) => {
      apply( up )
      println( nLine + " UnaryProof : " + sequentToString( r ) )
    }
    case TermEquivalenceRule1( up, r, _, _ ) => {
      apply( up )
      println( nLine + " UnaryProof : " + sequentToString( r ) )
    }
    case trsArrowRule( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case foldLeftRule( up, r, _, _ ) => {
      apply( up )
      println( nLine + p.rule + " : " + sequentToString( r ) )
    }
    case _ => println( "ERROR in printSchemaProof : " + p.rule )
  }
}
