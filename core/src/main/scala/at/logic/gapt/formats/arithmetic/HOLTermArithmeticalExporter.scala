/*
 * LambdaExpressionArithmeticalExporter.scala
 *
 */

package at.logic.gapt.formats.arithmetic

import at.logic.gapt.expr._
import at.logic.gapt.formats.{ HOLTermExporter, OutputExporter }
import at.logic.gapt.expr.schema.{ BigOr, BigAnd }

// FIXME: bad import, we don't want to import
// something from transformations here.
import at.logic.gapt.proofs.ceres_schema.struct.ClauseSetSymbol
import at.logic.gapt.proofs.ceres_schema.struct.TypeSynonyms.CutConfiguration

trait HOLTermArithmeticalExporter extends OutputExporter with HOLTermExporter {
  def exportFunction( t: LambdaExpression ): Unit = t match {
    case Top() => getOutput.write( "\\top" )
    case Bottom() => getOutput.write( "\\bot" )
    case HOLFunction( Const( "+", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " + " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( Const( "-", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " - " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( Const( "*", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " * " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( Const( """/""", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ / """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( Const( "<", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ < """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( Const( ">", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ > """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( Const( "=", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ = """ ); exportTerm( y ); getOutput.write( ")" ) }
    case BigAnd( v, f, s, e ) =>
      getOutput.write( "(" )
      getOutput.write( """\bigwedge_{""" )
      exportTerm( v )
      getOutput.write( " = " )
      exportTerm( s )
      getOutput.write( "}^{" )
      exportTerm( e )
      getOutput.write( "}" )
      exportTerm( f )
      getOutput.write( ")" )

    case BigOr( v, f, s, e ) =>
      getOutput.write( "(" )
      getOutput.write( """\bigvee_{""" )
      exportTerm( v )
      getOutput.write( " = " )
      exportTerm( s )
      getOutput.write( "}^{" )
      exportTerm( e )
      getOutput.write( "}" )
      exportTerm( f )
      getOutput.write( ")" )

    case HOLFunction( VarOrConst( name, _ ), args ) => {
      getOutput.write( name )
      getOutput.write( "(" )
      if ( args.size > 0 ) exportTerm( args.head )
      if ( args.size > 1 ) args.tail.foreach( x => { getOutput.write( "," ); exportTerm( x ) } )
      getOutput.write( ")" )
    }
    case HOLAtom( c, args ) => {
      val sym = c match {
        case h @ Const( _, _ ) => h.asInstanceOf[Const].sym
        case h @ Const( _, _ ) => h.asInstanceOf[Var].sym
      }

      var nonschematic = sym match {
        case cs: ClauseSetSymbol => {
          getOutput.write( "CL^{(" );

          writeCutConf( cs.cut_occs );
          getOutput.write( ")," );
          getOutput.write( cs.name );
          getOutput.write( "}_{" );
          getOutput.write( "{" );
          false;
        }
        case _ =>
          getOutput.write( sym.toString )
          true
      }
      if ( nonschematic ) {
        getOutput.write( "(" )
        getOutput.write( "{" )
      }

      if ( args.size > 0 ) exportTerm( args.head )
      if ( args.size > 1 ) args.tail.foreach( x => { getOutput.write( "," ); exportTerm( x ) } )

      if ( nonschematic ) {
        getOutput.write( ")}" )
      } else
        getOutput.write( "}}" )
    }
  }

  def exportSymbol( sym: SymbolA ): Unit = sym match {
    case cs: ClauseSetSymbol =>
      getOutput.write( "CL^{(" ); writeCutConf( cs.cut_occs );
      getOutput.write( ")," );
      getOutput.write( cs.name );
      getOutput.write( "}" )
    case _ => getOutput.write( sym.toString )
  }

  private def writeCutConf( cc: CutConfiguration ) = {
    if ( cc._1.size > 0 ) {
      exportTerm( cc._1.head );
      cc._1.tail.foreach( f => { getOutput.write( ", " ); exportTerm( f ) } )
    }
    getOutput.write( "|" )
    if ( cc._2.size > 0 ) {
      exportTerm( cc._2.head )
      cc._2.tail.foreach( f => { getOutput.write( ", " ); exportTerm( f ) } )
    }
  }
}
