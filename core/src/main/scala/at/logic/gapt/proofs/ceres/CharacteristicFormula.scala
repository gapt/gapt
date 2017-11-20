package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }

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
object RecursiveCharFormN {
  def apply( SCS: Map[Struct[Nothing], ( Struct[Nothing], Set[Var] )] ): Map[Formula, ( Formula, Set[Var] )] = {
    val names = constructingForm.structToformulaName( SCS )
    SCS.keySet.map( x => {
      val CLS( Apps( Const( name, _ ), vs ), cc ) = x
      val thefirst = vs.headOption.getOrElse( {
        throw new Exception( "Should not be empty" )
      } )
      val result = if ( freeVariables( thefirst ).isEmpty ) None else Some( freeVariables( thefirst ).head )
      val ( one, two ) = SCS.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      ( Atom( names.getOrElse( ( ( name, result ), cc ), {
        throw new Exception( "?????" )
      } ) + "PR", vs ), ( constructingForm( one, names ), two ) )
    } ).toMap
  }

  def MakePRReadyN( ChF: Map[Formula, ( Formula, Set[Var] )] ): Map[Expr, Set[( Formula, Formula )]] = {
    val preRes = ChF.keySet.map( x => {
      val ( one, two ) = ChF.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      ( x, two.foldLeft( one )( ( x, y ) => {
        Apps( ForallC( y.ty ), Abs( y, x ) ).asInstanceOf[Formula]
      } ) )
    } ).toMap
    val nextRes = preRes.keySet.map( x => {
      val one = preRes.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      val Atom( Const( name, _ ), vs ) = x
      ( Const( name, TArr( vs.tail.foldLeft( vs.head.ty )( ( x, y ) => TArr( x, y.ty ) ), To ) ).asInstanceOf[Expr], ( x, one ) )
    } )
    nextRes.foldLeft( Map[Expr, Set[( Formula, Formula )]]() )( ( x, y ) => {
      val ( one, ( two, three ) ) = y
      val theset = x.getOrElse( one, Set() ) ++ Set( ( two, three ) )
      x ++ Map( ( one, theset ) )
    } )
  }

  def AddToContext( ChF: Map[Expr, Set[( Formula, Formula )]] )( implicit ctx: MutableContext ): Unit = {
    ChF.keySet.foreach( x => {
      val one = ChF.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      val ret: ( Option[Expr], Option[Expr] ) = one.foldLeft( ( Option[Expr]( Atom( "", List() ) ), Option[Expr]( Atom( "", List() ) ) ) )( ( x, z ) => {
        val ( y, w ) = z
        val Atom( _, vs ) = y
        val zero = ctx.get[Context.Constants].constants.getOrElse( "0", {
          throw new Exception( "nat not defined" )
        } )
        if ( vs.head.equals( zero ) ) ( Some( Apps( EqC( y.ty ), Seq[Expr]( y, w ) ) ), x._2 )
        else ( x._1, Some( Apps( EqC( y.ty ), Seq[Expr]( y, w ) ) ) )
      } )
      val bc = ret._1.getOrElse( {
        throw new Exception( "?????" )
      } ).toString
      val sc = ret._2.getOrElse( {
        throw new Exception( "?????" )
      } ).toString
      ctx += PrimRecFun( x.asInstanceOf[Const], bc, sc )
    } )
  }
}