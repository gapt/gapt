package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._

import at.logic.gapt.expr.hol.toNNF
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }

object CharFormN extends StructVisitor[Formula, Unit] {
  def apply( struct: Struct ): Formula = recurse( struct, StructTransformer[Formula, Unit](
    { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) },
    { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Unit )
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
  private val stTN = StructTransformer[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]](
    { ( x, _ ) => x }, { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, _ ) => Neg( x ) }, Support.cF )
  def PR( ChF: Map[Formula, ( Formula, Set[Var] )] )( implicit ctx: MutableContext ): Unit = Support.add( ChF, ForallC )
}
object CharFormP extends StructVisitor[Formula, Unit] {
  def apply( struct: Struct ): Formula = recurse( struct, StructTransformer[Formula, Unit](
    { ( x, _ ) => toNNF( Neg( x ) ) }, { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, _ ) => Neg( x ) },
    { ( _, _, _ ) => throw new Exception( "Should not contain CLS terms" ) } ), Unit )
}
object CharFormPRP {
  def apply( SCS: Map[CLS, ( Struct, Set[Var] )] ): Map[Formula, ( Formula, Set[Var] )] = Support( SCS, stTP )
  private val stTP = StructTransformer[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]](
    { ( x, _ ) => Neg( x ) }, { ( x, y, _ ) => Or( x, y ) }, Bottom(), { ( x, y, _ ) => And( x, y ) }, Top(), { ( x, _ ) => Neg( x ) }, Support.cF )
  def PR( ChF: Map[Formula, ( Formula, Set[Var] )] )( implicit ctx: MutableContext ): Unit = Support.add( ChF, ExistsC )
}

private object Support {
  def apply(
    SCS: Map[CLS, ( Struct, Set[Var] )],
    stT: StructTransformer[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]] ): Map[Formula, ( Formula, Set[Var] )] = {
    val names = structNames( SCS )
    SCS.keySet.map( x => {
      val CLS( Apps( Const( name, _ ), vs ), cc ) = x
      val thefirst = vs.headOption.getOrElse( {
        throw new Exception( "Should not be empty" )
      } )
      val result = freeVariables( thefirst ).headOption
      val ( one, two ) = SCS( x )
      ( Atom( names( ( ( name, result ), cc ) ) + "PR", vs ), ( constructingForm( one, names, stT ), two ) )
    } ).toMap
  }

  def cF( pn: Expr, cc: Sequent[Boolean], mn: Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String] ): Formula = {
    val Apps( Const( name, _ ), vs ) = pn
    val thefirst = vs.headOption.getOrElse( { throw new Exception( "Should not be empty" ) } )
    val result: Option[Expr] = freeVariables( thefirst ).headOption
    Atom( mn.getOrElse( ( ( name, result ), cc ), { throw new Exception( "Should be in map" ) } ) + "PR", vs )
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
  def add( ChF: Map[Formula, ( Formula, Set[Var] )], qType: QuantifierC )( implicit ctx: MutableContext ): Unit = {
    val preRes = ChF.keySet.map( x => {
      val ( one, two ) = ChF.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      ( x, if ( qType.equals( ForallC ) ) QuantIntroForAll( one, two ) else QuantIntroExists( one, two ) )
    } ).toMap
    val ( namecha, nextRes ) = preRes.keySet.map( x => {
      val one = preRes.getOrElse( x, {
        throw new Exception( "?????" )
      } )
      val Atom( Const( name, _ ), vs ) = x
      val newEx = Const( name, FunctionType( To, vs.map { _.ty } ) ).asInstanceOf[Expr]
      ( ( name.substring( 0, name.length - 2 ), newEx ), ( newEx, ( Apps( newEx, vs: _* ), one ) ) )
    } ).toList.unzip
    val namesdis = namecha.toSet
    addToContextAsPRDefs( nextRes.map {
      case ( x, ( y, z ) ) =>
        ( x, ( y, namesdis.foldLeft( z: Expr )( ( w, r ) => {
          TermReplacement( w, { case Const( n, _ ) if n == r._1 => r._2 } )
        } ) ) )
    }.foldLeft( Map[Expr, Set[( Expr, Expr )]]() ) {
      case ( x, ( one, ( two, three ) ) ) => {
        val theset = x.getOrElse( one, Set() ) ++ Set( ( two, three ) )
        x ++ Map( ( one, theset ) )
      }
    } )
  }
  private def structNames( sss: Map[CLS, ( Struct, Set[Var] )] ): Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String] =
    sss.keySet.map {
      case CLS( Apps( Const( name, _ ), vs ), cc ) =>
        val thefirst = vs.headOption.getOrElse( { throw new Exception( "Should not be empty" ) } )
        val result: Option[Expr] = freeVariables( thefirst ).headOption
        val cutConfigChars = cc.map( b => if ( b ) 'T' else 'F' )
        val newName: String = name + "S" ++ cutConfigChars.succedent + "A" ++ ( cutConfigChars.antecedent )
        ( ( ( name, result ), cc ), newName )
    }.toMap
  private def addToContextAsPRDefs( ChF: Map[Expr, Set[( Expr, Expr )]] )( implicit ctx: MutableContext ): Unit = {
    val prDefsForContext = for ( ( pred, _ ) <- ChF ) yield ( pred.asInstanceOf[Const], Seq( ChF( pred ).foldLeft( ( Some[Expr]( Atom( "", List() ) ), Some[Expr]( Atom( "", List() ) ) ) ) {
      case ( x, ( y, w ) ) => {
        val zero = ctx.get[Context.Constants].constants.getOrElse( "0", {
          throw new Exception( "nat not defined" + ctx.get[Context.Constants].constants.toString() )
        } )
        val Atom( _, vs ) = y
        if ( vs.head.equals( zero ) ) ( Some( y === w ), x._2 )
        else ( x._1, Some( Apps( EqC( y.ty ), Seq[Expr]( y, w ) ) ) )
      }
    } ).map {
      case ( optBc, optSc ) => Seq( optBc.getOrElse( {
        throw new Exception( "?????" )
      } ).toString, optSc.getOrElse( {
        throw new Exception( "?????" )
      } ).toString )
    }.head )
    ctx += PrimRecFun( prDefsForContext.toSet )
  }
  private object constructingForm extends StructVisitor[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]] {
    def apply( struct: Struct, names: Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String],
               stT: StructTransformer[Formula, Map[( ( String, Option[Expr] ), Sequent[Boolean] ), String]] ): Formula =
      recurse( struct, stT, names )
  }
}