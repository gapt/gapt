package gapt.examples

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.ceres._

object OneStrictMonotoneTwoFunctionRefutation extends TacticsProof( OneStrictMonotoneTwoFunctionSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "omega" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  def sequentForm( input: Expr ) = Viperize( le"omegaSFAF $input" )
}
