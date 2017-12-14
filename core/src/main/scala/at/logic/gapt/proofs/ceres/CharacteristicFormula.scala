package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.toNNF
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }

object CharFormN extends StructVisitor[Formula, Unit] {
  def apply( struct: Struct ): Formula = {
    val csf = recurse( struct, StructTransformer[Formula, Unit](
      { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) }, { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Unit )
    new QuantifierHelper( ForallC ).Block( freeVariables( csf ).toSeq, csf )
  }
}
object CharFormPRN {
  def apply( SCS: Map[CLS, ( Struct, Set[Var] )] ): Map[Formula, ( Formula, Set[Var] )] = Support(
    SCS, stTN )
  private def SCSinCNF( st: Struct ): Struct = st match {
    case Plus( x, Times( y, z ) ) => Times( Plus( SCSinCNF( x ), SCSinCNF( y ) ), Plus( SCSinCNF( x ), SCSinCNF( z ) ) )
    case Plus( Times( y, z ), x ) => Times( Plus( SCSinCNF( y ), SCSinCNF( x ) ), Plus( SCSinCNF( z ), SCSinCNF( x ) ) )
    case Plus( x, y )             => Plus( SCSinCNF( x ), SCSinCNF( y ) )
    case Times( x, y )            => Times( SCSinCNF( x ), SCSinCNF( y ) )
    case Dual( x )                => Dual( SCSinCNF( x ) )
    case x                        => x
  }
  private val stTN = StructTransformer[Formula, Map[( String, Sequent[Boolean] ), String]](
    { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) }, Support.cF )
  def PR( chF: Map[Formula, ( Formula, Set[Var] )] )( implicit ctx: MutableContext ): Unit = Support.add( chF, ForallC )
}
object CharFormP extends StructVisitor[Formula, Unit] {
  def apply( struct: Struct ): Formula = {
    val csf = recurse( struct, StructTransformer[Formula, Unit](
      { ( x, _ ) => toNNF( Neg( x ) ) }, { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, _ ) => Neg( x ) }, { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Unit )
    new QuantifierHelper( ExistsC ).Block( freeVariables( csf ).toSeq, csf )
  }
}
object CharFormPRP {
  def apply( SCS: Map[CLS, ( Struct, Set[Var] )] ): Map[Formula, ( Formula, Set[Var] )] = Support( SCS, stTP )
  private val stTP = StructTransformer[Formula, Map[( String, Sequent[Boolean] ), String]](
    { ( x, _ ) => Neg( x ) }, { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, _ ) => Neg( x ) }, Support.cF )
  def PR( chF: Map[Formula, ( Formula, Set[Var] )] )( implicit ctx: MutableContext ): Unit = Support.add( chF, ExistsC )
}

private object Support {
  def apply(
    SCS: Map[CLS, ( Struct, Set[Var] )],
    stT: StructTransformer[Formula, Map[( String, Sequent[Boolean] ), String]] ): Map[Formula, ( Formula, Set[Var] )] = {
    val names = structNames( SCS )
    SCS.keySet.map( x => {
      val CLS( Apps( Const( name, _ ), vs ), cc ) = x
      val ( one, two ) = SCS( x )
      ( Atom( names( ( name, cc ) ) + "PR", vs ), ( constructingForm( one, names, stT ), two ) )
    } ).toMap
  }

  def cF( pn: Expr, cc: Sequent[Boolean], mn: Map[( String, Sequent[Boolean] ), String] ): Formula = {
    val Apps( Const( name, _ ), vs ) = pn
    Atom( mn.getOrElse( ( name, cc ), { throw new Exception( "Should be in map" ) } ) + "PR", vs )
  }
  //assuming NNFCNF
  private def QuantIntroForAll( f: Formula, evar: Set[Var] ): Formula = f match {
    case And( x, And( Top(), Top() ) )          => QuantIntroForAll( x, evar )
    case And( And( Top(), Top() ), x )          => QuantIntroForAll( x, evar )
    case And( Top(), x )                        => QuantIntroForAll( x, evar )
    case And( x, Top() )                        => QuantIntroForAll( x, evar )
    case And( x, y )                            => And( QuantIntroForAll( x, evar ), QuantIntroForAll( y, evar ) )
    case Or( x, Or( Bottom(), Bottom() ) )      => QuantIntroForAll( x, evar )
    case Or( Or( Bottom(), Bottom() ), x )      => QuantIntroForAll( x, evar )
    case Or( Bottom(), x )                      => QuantIntroForAll( x, evar )
    case Or( x, Bottom() )                      => QuantIntroForAll( x, evar )
    case Or( Neg( Neg( x ) ), Neg( Neg( y ) ) ) => new QuantifierHelper( ForallC ).Block( evar.intersect( freeVariables( Or( x, y ) ) ).toSeq, Or( x, y ) )
    case Or( x, Neg( Neg( y ) ) )               => new QuantifierHelper( ForallC ).Block( evar.intersect( freeVariables( Or( x, y ) ) ).toSeq, Or( x, y ) )
    case Or( Neg( Neg( x ) ), y )               => new QuantifierHelper( ForallC ).Block( evar.intersect( freeVariables( Or( x, y ) ) ).toSeq, Or( x, y ) )
    case Or( x, y )                             => new QuantifierHelper( ForallC ).Block( evar.intersect( freeVariables( Or( x, y ) ) ).toSeq, Or( x, y ) )
    case Atom( _, _ )                           => new QuantifierHelper( ForallC ).Block( evar.intersect( freeVariables( f ) ).toSeq, f )
    case Top()                                  => Top()
    case Bottom()                               => Bottom()
    case Neg( Neg( x ) )                        => Neg( QuantIntroForAll( x, evar ) )
    case Neg( x )                               => Neg( QuantIntroForAll( x, evar ) )
  }
  private def QuantIntroExists( f: Formula, evar: Set[Var] ): Formula = f match {
    case Or( x, Or( Bottom(), Bottom() ) )       => QuantIntroExists( x, evar )
    case Or( Or( Bottom(), Bottom() ), x )       => QuantIntroExists( x, evar )
    case Or( Bottom(), x )                       => QuantIntroExists( x, evar )
    case Or( x, Bottom() )                       => QuantIntroExists( x, evar )
    case Or( x, y )                              => Or( QuantIntroExists( x, evar ), QuantIntroExists( y, evar ) )
    case And( x, And( Top(), Top() ) )           => QuantIntroExists( x, evar )
    case And( And( Top(), Top() ), x )           => QuantIntroExists( x, evar )
    case And( Top(), x )                         => QuantIntroExists( x, evar )
    case And( x, Top() )                         => QuantIntroExists( x, evar )
    case And( Neg( Neg( x ) ), Neg( Neg( y ) ) ) => new QuantifierHelper( ExistsC ).Block( evar.intersect( freeVariables( And( x, y ) ) ).toSeq, And( x, y ) )
    case And( x, Neg( Neg( y ) ) )               => new QuantifierHelper( ExistsC ).Block( evar.intersect( freeVariables( And( x, y ) ) ).toSeq, And( x, y ) )
    case And( Neg( Neg( x ) ), y )               => new QuantifierHelper( ExistsC ).Block( evar.intersect( freeVariables( And( x, y ) ) ).toSeq, And( x, y ) )
    case And( x, y )                             => new QuantifierHelper( ExistsC ).Block( evar.intersect( freeVariables( And( x, y ) ) ).toSeq, And( x, y ) )
    case Atom( _, _ )                            => new QuantifierHelper( ExistsC ).Block( evar.intersect( freeVariables( f ) ).toSeq, f )
    case Top()                                   => Top()
    case Bottom()                                => Bottom()
    case Neg( Neg( x ) )                         => QuantIntroExists( x, evar )
    case Neg( x )                                => Neg( QuantIntroExists( x, evar ) )
  }
  def add( chF: Map[Formula, ( Formula, Set[Var] )], qType: QuantifierC )( implicit ctx: MutableContext ): Unit = {
    val preRes = for ( ( x, ( form, vars ) ) <- chF ) yield ( x, if ( qType.equals( ForallC ) ) QuantIntroForAll( form, vars ) else QuantIntroExists( form, vars ) )
    val changeRes = for {
      ( Atom( Const( name, _ ), vs ), form2 ) <- preRes.toList
      newEx = Const( name, FunctionType( To, vs.map { _.ty } ) )
    } yield ( ( name.substring( 0, name.length - 2 ), newEx ), ( newEx, ( Apps( newEx, vs: _* ), form2 ) ) )
    val ( nameCha, nextRes ) = changeRes.unzip
    val namedis = nameCha.toMap
    addToContextAsPRDefs( nextRes.map {
      case ( x, ( y, z ) ) => ( x, ( y, TermReplacement( z, { case Const( n, _ ) if namedis.contains( n ) => namedis( n ) } ).asInstanceOf[Expr] ) )
    }.groupBy( _._1 ).map { case ( pred, eqns ) => ( pred, eqns.map( _._2 ).toSet ) } )
  }
  private def structNames( sss: Map[CLS, ( Struct, Set[Var] )] ): Map[( String, Sequent[Boolean] ), String] =
    sss.keySet.map {
      case CLS( Apps( Const( name, _ ), _ ), cc ) =>
        val cutConfigChars = cc.map( b => if ( b ) 'T' else 'F' )
        val newName: String = name + "S" ++ cutConfigChars.succedent + "A" ++ cutConfigChars.antecedent
        ( ( name, cc ), newName )
    }.toMap
  private def addToContextAsPRDefs( chF: Map[Const, Set[( Expr, Expr )]] )( implicit ctx: MutableContext ): Unit =
    ctx += PrimRecFun( chF )
  private object constructingForm extends StructVisitor[Formula, Map[( String, Sequent[Boolean] ), String]] {
    def apply( struct: Struct, names: Map[( String, Sequent[Boolean] ), String],
               stT: StructTransformer[Formula, Map[( String, Sequent[Boolean] ), String]] ): Formula =
      recurse( struct, stT, names )
  }
}