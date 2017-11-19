package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent

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

private object constructingForm extends StructVisitor[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]] {
  def apply[Data]( struct: Struct[Data], names: Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String] ): Formula = recurse( struct, StructTransformer[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]](
    { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) }, { ( pn, cc, mn ) =>
      {
        val Apps( Const( name, _ ), vs ) = pn
        val thefirst = vs.headOption.getOrElse( { throw new Exception( "Should not be empty" ) } )
        val result: Option[Expr] = if ( freeVariables( thefirst ).isEmpty ) None else Some( freeVariables( thefirst ).head )
        Atom( mn.getOrElse( ( ( name, result ), cc ), { throw new Exception( "Should be in map" ) } ), vs )
      }
    } ), names )

  def structToformulaName( sss: Map[Struct[Nothing], ( Struct[Nothing], Set[Var] )] ): Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String] =
    sss.keySet.map {
      case CLS( Apps( Const( name, _ ), vs ), cc ) =>
        val thefirst = vs.headOption.getOrElse( { throw new Exception( "Should not be empty" ) } )
        val result: Option[Expr] = if ( freeVariables( thefirst ).isEmpty ) None else Some( freeVariables( thefirst ).head )
        ( ( ( name, result ), cc ), name )
    }.toMap
}
object RecursiveCharForm {
  def apply( SCS: Map[Struct[Nothing], ( Struct[Nothing], Set[Var] )] ): Map[Formula, ( Formula, Set[Var] )] = {
    val names = constructingForm.structToformulaName( SCS )
    SCS.keySet.map( x => {
      val CLS( Apps( Const( name, _ ), vs ), cc ) = x
      val thefirst = vs.headOption.getOrElse( { throw new Exception( "Should not be empty" ) } )
      val result = if ( freeVariables( thefirst ).isEmpty ) None else Some( freeVariables( thefirst ).head )
      val ( one, two ) = SCS.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      ( Atom( names.getOrElse( ( ( name, result ), cc ), { throw new Exception( "?????" ) } ), vs ), ( constructingForm( one, names ), two ) )
    } ).toMap
  }
}