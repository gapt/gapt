package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._

object CharacteristicFormulaN extends StructVisitor[Formula, List[Nothing]] {
  def apply[Data]( struct: Struct[Data] ): Formula = recurse( struct, StructTransformer[Formula, List[Nothing]](
    { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) },
    { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Nil )
}

object CharacteristicFormulaP extends StructVisitor[Formula, List[Nothing]] {
  def apply[Data]( struct: Struct[Data] ): Formula = recurse( struct, StructTransformer[Formula, List[Nothing]](
    { ( x, _ ) => x }, { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, _ ) => Neg( x ) },
    { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Nil )
}

