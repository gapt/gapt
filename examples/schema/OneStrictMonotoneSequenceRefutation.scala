package gapt.examples

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.ceres._

object OneStrictMonotoneSequenceRefutation extends TacticsProof( OneStrictMonotoneSequenceSchema.ctx ) {
  val SCS: Map[CLS, ( Struct, Set[Var] )] = SchematicStruct( "Top" ).getOrElse( Map() )
  val CFPRN = CharFormPRN( SCS )
  CharFormPRN.PR( CFPRN )
  def sequentForm( input: Expr ) = Viperize( le"TopSFAF $input" )
}
