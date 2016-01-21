package at.logic.gapt.examples.poset
import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.examples.Script
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.grammars.{ findMinimalVectGrammar, VectTratGrammar }
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.lk._
import at.logic.gapt.expr._
import at.logic.gapt.cutintro.{ ReforestMethod, GrammarFindingMethod, MaxSATMethod, CutIntroduction }
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.maxsat.ExternalMaxSATSolver
import at.logic.gapt.provers.prover9.Prover9

object atp_instances extends Script {

  val f = FOLFunctionConst( "f", 2 )
  val Seq( u, v, w, x, y, z ) = Seq( "u", "v", "w", "x", "y", "z" ) map { FOLVar( _ ) }
  val Seq( a, b, c ) = Seq( "a", "b", "c" ) map { FOLConst( _ ) }

  val eqRefl = All( x, x === x )
  val eqSymm = All( x, All( y, ( x === y ) --> ( y === x ) ) )
  val eqTran = All( x, All( y, All( z, ( ( x === y ) & ( y === z ) ) --> ( x === z ) ) ) )
  val eqFCongr = All( x, All( y, All( u, All( v, ( ( x === y ) & ( u === v ) ) --> ( f( x, u ) === f( y, v ) ) ) ) ) )

  val fComm = All( x, All( y, f( x, y ) === f( y, x ) ) )
  val fAssoc = All( x, All( y, All( z, f( f( x, y ), z ) === f( x, f( y, z ) ) ) ) )

  val fAntiSym = All( u, All( v, ( ( f( u, v ) === u ) & ( f( v, u ) === v ) ) --> ( u === v ) ) )
  val fTrans = All( x, All( y, All( z, ( ( f( x, y ) === x ) & ( f( y, z ) === y ) ) --> ( f( x, z ) === x ) ) ) )

  val concl = ( ( f( a, b ) === a ) & ( f( b, c ) === b ) & ( f( c, a ) === c ) ) --> ( ( a === b ) & ( b === c ) )

  val endSequent = eqRefl +: eqSymm +: eqTran +: eqFCongr +: fComm +: fAssoc +: Sequent() :+ concl

  val removeEq = Map[LambdaExpression, LambdaExpression]( EqC( Ti ) -> FOLAtomConst( "E", 2 ) )
  val endSequentWoEq = endSequent map {
    TermReplacement( _, removeEq )
  }

  val Some( p ) = Prover9 getLKProof endSequentWoEq map {
    TermReplacement( _, removeEq map { _.swap } )
  }
  //val Some(p) = Prover9 getLKProof { fComm +: fAssoc +: Sequent() :+ concl }
  InstanceTermEncoding( p )._1 foreach println

  CutIntroduction.compressLKProof(
    p,
    //  method = ReforestMethod(),
    method = new GrammarFindingMethod {
    override def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
      Some( findMinimalVectGrammar( lang, Seq( 3 ),
        maxSATSolver = new ExternalMaxSATSolver( "open-wbo", "-cpu-lim=100", "-algorithm=1" ),
        weight = _._1.size ) )
    }

    override def name = "wmaxsat_3"
  },
    verbose = true
  )
}
