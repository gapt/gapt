/*
 * HOLExpressionArithmeticalExporter.scala
 *
 */

package at.logic.gapt.formats.arithmetic

import at.logic.gapt.language.hol._
import at.logic.gapt.language.hol.logicSymbols._
import at.logic.gapt.expr.symbols.SymbolA
import at.logic.gapt.language.schema.{ SchemaTopC, SchemaBottomC, BigAnd, BigOr, SchemaFormula }
import at.logic.gapt.language.schema.logicSymbols.BiggerThanSymbol
import at.logic.gapt.formats.{ HOLTermExporter, OutputExporter }

// FIXME: bad import, we don't want to import
// something from transformations here.
import at.logic.gapt.proofs.algorithms.ceres.struct.ClauseSetSymbol
import at.logic.gapt.proofs.algorithms.ceres.struct.TypeSynonyms.CutConfiguration

trait HOLTermArithmeticalExporter extends OutputExporter with HOLTermExporter {
  def exportFunction( t: HOLExpression ): Unit = t match {
    case SchemaTopC => getOutput.write( "\\top" )
    case SchemaBottomC => getOutput.write( "\\bot" )
    case HOLFunction( HOLConst( "+", _ ), x :: y :: Nil, _ ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " + " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( HOLConst( "-", _ ), x :: y :: Nil, _ ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " - " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( HOLConst( "*", _ ), x :: y :: Nil, _ ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( " * " ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLFunction( HOLConst( """/""", _ ), x :: y :: Nil, _ ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ / """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( HOLConst( "<", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ < """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( HOLConst( ">", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ > """ ); exportTerm( y ); getOutput.write( ")" ) }
    case HOLAtom( HOLConst( "=", _ ), x :: y :: Nil ) => { getOutput.write( "(" ); exportTerm( x ); getOutput.write( """ = """ ); exportTerm( y ); getOutput.write( ")" ) }
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

    case HOLFunction( VarOrConst( name, _ ), args, _ ) => {
      getOutput.write( name )
      getOutput.write( "(" )
      if ( args.size > 0 ) exportTerm( args.head )
      if ( args.size > 1 ) args.tail.foreach( x => { getOutput.write( "," ); exportTerm( x ) } )
      getOutput.write( ")" )
    }
    case HOLAtom( c, args ) => {
      val sym = c match {
        case h @ HOLConst( _, _ ) => h.asInstanceOf[HOLConst].sym
        case h @ HOLConst( _, _ ) => h.asInstanceOf[HOLVar].sym
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
