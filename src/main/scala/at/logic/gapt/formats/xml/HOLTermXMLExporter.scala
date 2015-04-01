/*
 * HOLExpressionExporter.scala
 *
 */

package at.logic.gapt.formats.xml

import at.logic.gapt.formats.ExportingException
import at.logic.gapt.language.hol._
import at.logic.gapt.language.lambda.types.{ ->, FunctionType, Ti, To }

trait HOLTermXMLExporter {
  def exportTerm( term: HOLExpression ): scala.xml.Elem = term match {
    case HOLAtom( c: HOLConst, args ) =>
      <constantatomformula symbol={ c.name.toString }>
        { exportList( args ) }
      </constantatomformula>
    case HOLAtom( c: HOLVar, args ) =>
      <variableatomformula>
        { exportList( c :: args ) }
      </variableatomformula>
    //defined sets need to be matched before general functions
    case HOLFunction( HOLConst( a, FunctionType( To, ls ) ), args, rtype ) if ( ls.last == Ti ) =>
      <definedset definition={ a } symbol={ a }>
        { exportList( args ) }
      </definedset>
    // TODO Function with HOLVar
    case HOLFunction( f: HOLConst, args, _ ) =>
      <function symbol={ f.name.toString }>
        { exportList( args ) }
      </function>
    case HOLAnd( left, right ) =>
      <conjunctiveformula type="and">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case HOLOr( left, right ) =>
      <conjunctiveformula type="or">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case HOLImp( left, right ) =>
      <conjunctiveformula type="impl">
        { exportList( left :: right :: Nil ) }
      </conjunctiveformula>
    case HOLNeg( f ) =>
      <conjunctiveformula type="neg">
        { exportTerm( f ) }
      </conjunctiveformula>
    case HOLAllVar( vr @ HOLVar( _, Ti ), f ) =>
      <quantifiedformula type="all">
        { exportList( vr :: f :: Nil ) }
      </quantifiedformula>
    case HOLExVar( vr @ HOLVar( _, Ti ), f ) =>
      <quantifiedformula type="exists">
        { exportList( vr :: f :: Nil ) }
      </quantifiedformula>
    case HOLAllVar( vr @ HOLVar( _, ->( Ti, To ) ), f ) =>
      <secondorderquantifiedformula type="all">
        { exportList( vr :: f :: Nil ) }
      </secondorderquantifiedformula>
    case HOLExVar( vr @ HOLVar( _, ->( Ti, To ) ), f ) =>
      <secondorderquantifiedformula type="exists">
        { exportList( vr :: f :: Nil ) }
      </secondorderquantifiedformula>
    // TODO: variables and constants of other types
    case HOLVar( a, Ti ) =>
      <variable symbol={ a.toString }/>
    case HOLVar( a, ->( Ti, To ) ) =>
      <secondordervariable symbol={ a.toString }/>
    case HOLConst( a, Ti ) =>
      <constant symbol={ a.toString }/>

    /*
    case AppN1(Var(ConstantStringSymbol(a),FunctionType(Ti(),_)),args) =>
      <function symbol={a}>
        {exportList(args)}
      </function>
    case Var(VariableStringSymbol(a), ->(Ti(),To())) =>
      <secondordervariable symbol={a}/>
      */
    case HOLAbsN1( varlist, func ) =>
      <lambdasubstitution>
        <variablelist>
          { exportList( varlist ) }
        </variablelist>{ exportTerm( func ) }
      </lambdasubstitution>
    case _ => throw new ExportingException( "Term cannot be exported into the required xml format: " + term.toString )
  }
  private def exportList( ls: List[HOLExpression] ) = ls.map( x => exportTerm( x ) )
}

private object HOLAbsN {
  def unapply( e: HOLExpression ): Option[( List[HOLVar], HOLExpression )] = e match {
    case HOLAbs( x, e1 ) =>
      val Some( ( vs, re ) ) = unapply( e1 ); Some( ( x :: vs, re ) )
    case _ => Some( ( Nil, e ) )
  }
}

private object HOLAbsN1 {
  def unapply( e: HOLExpression ): Option[( List[HOLVar], HOLExpression )] = e match {
    case HOLAbsN( vs, e1 ) if vs.nonEmpty =>
      Some( ( vs, e1 ) )
    case _ => None
  }
}
