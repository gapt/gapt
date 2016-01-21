/*
 * LambdaExpressionLatexExporter.scala
 *
 */

package at.logic.gapt.formats.latex

import at.logic.gapt.formats.{ HOLTermExporter, OutputExporter }
import at.logic.gapt.expr._
import at.logic.gapt.expr.schema.indexedOmegaVar

trait HOLTermLatexExporter extends OutputExporter with HOLTermExporter {
  // it is LambdaExpression and require because of the stupid design chose not to have a common element for HOL
  def exportTerm( t: LambdaExpression ): Unit = {
    require( t.isInstanceOf[LambdaExpression] );
    t match {
      case indexedOmegaVar( name, index ) => getOutput.write( name + """_{""" + index + """}""" )
      case Var( name, _ )                 => getOutput.write( name.toString )
      case Const( name, _ )               => getOutput.write( name.toString )
      case Neg( f )                       => { getOutput.write( """\neg """ ); exportTerm_( f ); }
      case And( f1, f2 )                  => { exportTerm_( f1 ); getOutput.write( """ \wedge """ ); exportTerm_( f2 ); }
      case Or( f1, f2 )                   => { exportTerm_( f1 ); getOutput.write( """ \vee """ ); exportTerm_( f2 ); }
      case Imp( f1, f2 )                  => { exportTerm_( f1 ); getOutput.write( """ \rightarrow """ ); exportTerm_( f2 ); }
      case Ex( v, f )                     => { getOutput.write( """\exists """ ); exportTerm_( v.asInstanceOf[Var] ); getOutput.write( """.""" ); exportTerm_( f ); }
      case All( v, f )                    => { getOutput.write( """\forall """ ); exportTerm_( v.asInstanceOf[Var] ); getOutput.write( """.""" ); exportTerm_( f ); }
      case Abs( v, t )                    => { getOutput.write( """\lambda """ ); exportTerm_( v ); getOutput.write( """.""" ); exportTerm_( t ); }
      case HOLAtom( name, args )          => exportFunction( t )
      case HOLFunction( name, args )      => exportFunction( t )
    }
  }

  private def exportTerm_( t: LambdaExpression ): Unit = {
    require( t.isInstanceOf[LambdaExpression] ); t match {
      case indexedOmegaVar( name, index ) => getOutput.write( name + """_{""" + index + """}""" )
      case Var( name, _ )                 => getOutput.write( name.toString )
      case Const( name, _ )               => getOutput.write( name.toString )
      case Neg( f )                       => { getOutput.write( "(" ); getOutput.write( """\neg """ ); exportTerm_( f ); getOutput.write( ")" ) }
      case And( f1, f2 )                  => { getOutput.write( "(" ); exportTerm_( f1 ); getOutput.write( """ \wedge """ ); exportTerm_( f2 ); getOutput.write( ")" ) }
      case Or( f1, f2 )                   => { getOutput.write( "(" ); exportTerm_( f1 ); getOutput.write( """ \vee """ ); exportTerm_( f2 ); getOutput.write( ")" ) }
      case Imp( f1, f2 )                  => { getOutput.write( "(" ); exportTerm_( f1 ); getOutput.write( """ \rightarrow """ ); exportTerm_( f2 ); getOutput.write( ")" ) }
      case Ex( v, f )                     => { getOutput.write( "(" ); getOutput.write( """\exists """ ); exportTerm_( v.asInstanceOf[Var] ); getOutput.write( """.""" ); exportTerm_( f ); getOutput.write( ")" ) }
      case All( v, f )                    => { getOutput.write( "(" ); getOutput.write( """\forall """ ); exportTerm_( v.asInstanceOf[Var] ); getOutput.write( """.""" ); exportTerm_( f ); getOutput.write( ")" ) }
      case Abs( v, t )                    => { getOutput.write( "(" ); getOutput.write( """\lambda """ ); exportTerm_( v ); getOutput.write( """.""" ); exportTerm_( t ); getOutput.write( ")" ) }
      case HOLAtom( name, args )          => exportFunction( t )
      case HOLFunction( name, args )      => exportFunction( t )
    }
  }

  protected def latexType( ta: Ty ): String = ta match {
    case Ti           => "i"
    case To           => "o"
    case `->`( a, b ) => "(" + latexType( a ) + """ \rightarrow """ + latexType( b ) + ")"
  }
}

