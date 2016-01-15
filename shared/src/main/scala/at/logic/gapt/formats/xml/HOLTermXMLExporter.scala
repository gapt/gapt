/*
 * LambdaExpressionExporter.scala
 *
 */

package at.logic.gapt.formats.xml

import at.logic.gapt.formats.ExportingException
import at.logic.gapt.expr._
import at.logic.gapt.expr._

trait HOLTermXMLExporter {
  def exportTerm( term: LambdaExpression ): scala.xml.Elem = term match {
    case And( left, right ) =>
      <conjunctiveformula type="and">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case Or( left, right ) =>
      <conjunctiveformula type="or">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case Imp( left, right ) =>
      <conjunctiveformula type="impl">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case Neg( f ) =>
      <conjunctiveformula type="neg">
        { exportTerm( f ) }
      </conjunctiveformula>
    case All( vr @ Var( _, Ti ), f ) =>
      <quantifiedformula type="all">
        { exportList( vr :: f :: Nil ) }
      </quantifiedformula>
    case Ex( vr @ Var( _, Ti ), f ) =>
      <quantifiedformula type="exists">
        { exportList( vr :: f :: Nil ) }
      </quantifiedformula>
    case All( vr @ Var( _, `->`( Ti, To ) ), f ) =>
      <secondorderquantifiedformula type="all">
        { exportList( vr :: f :: Nil ) }
      </secondorderquantifiedformula>
    case Ex( vr @ Var( _, `->`( Ti, To ) ), f ) =>
      <secondorderquantifiedformula type="exists">
        { exportList( vr :: f :: Nil ) }
      </secondorderquantifiedformula>
    // TODO: variables and constants of other types
    case Var( a, Ti ) =>
      <variable symbol={ a.toString }/>
    case Var( a, `->`( Ti, To ) ) =>
      <secondordervariable symbol={ a.toString }/>
    case Const( a, Ti ) =>
      <constant symbol={ a.toString }/>
    case HOLAtom( c: Const, args ) =>
      <constantatomformula symbol={ c.name.toString }>
        { exportList( args ) }
      </constantatomformula>
    case HOLAtom( c: Var, args ) =>
      <variableatomformula>
        { exportList( c :: args ) }
      </variableatomformula>
    //defined sets need to be matched before general functions
    case HOLFunction( Const( a, FunctionType( To, ls ) ), args ) if ( ls.last == Ti ) =>
      <definedset definition={ a } symbol={ a }>
        { exportList( args ) }
      </definedset>
    // TODO Function with Var
    case HOLFunction( f: Const, args ) =>
      <function symbol={ f.name.toString }>
        { exportList( args ) }
      </function>

    /*
    case AppN1(Var(ConstantStringSymbol(a),FunctionType(Ti(),_)),args) =>
      <function symbol={a}>
        {exportList(args)}
      </function>
    case Var(VariableStringSymbol(a), ->(Ti(),To())) =>
      <secondordervariable symbol={a}/>
      */
    case AbsN1( varlist, func ) =>
      <lambdasubstitution>
        <variablelist>
          { exportList( varlist ) }
        </variablelist>{ exportTerm( func ) }
      </lambdasubstitution>
    case _ => throw new ExportingException( "Term cannot be exported into the required xml format: " + term.toString )
  }
  private def exportList( ls: List[LambdaExpression] ) = ls.map( x => exportTerm( x ) )
}

private object AbsN {
  def unapply( e: LambdaExpression ): Option[( List[Var], LambdaExpression )] = e match {
    case Abs( x, e1 ) =>
      val Some( ( vs, re ) ) = unapply( e1 ); Some( ( x :: vs, re ) )
    case _ => Some( ( Nil, e ) )
  }
}

private object AbsN1 {
  def unapply( e: LambdaExpression ): Option[( List[Var], LambdaExpression )] = e match {
    case AbsN( vs, e1 ) if vs.nonEmpty =>
      Some( ( vs, e1 ) )
    case _ => None
  }
}
