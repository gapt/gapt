package gapt.examples

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.ceres._

object ThreeStrictMonotoneRefutation extends TacticsProof( ThreeStrictMonotoneSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "omega" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  def sequentForm( input: Expr ) = Viperize( le"omegaSFAF $input" )
}
