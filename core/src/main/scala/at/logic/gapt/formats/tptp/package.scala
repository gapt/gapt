package at.logic.gapt.formats

import at.logic.gapt.expr._

package object tptp {

  type GeneralTerm = LambdaExpression
  type FormulaRole = String
  type InfoItem = GeneralTerm

  case class TptpFile( inputs: Seq[TptpInput] ) {
    override def toString = inputs.mkString
  }
  sealed trait TptpInput {
    override def toString = tptpToString.tptpInput( this )
  }
  case class AnnotatedFormula( language: String, name: String, role: FormulaRole, formula: HOLFormula, annotations: Seq[GeneralTerm] ) extends TptpInput
  case class IncludeDirective( fileName: String, formulaSelection: Option[Seq[String]] ) extends TptpInput

  object TptpTerm {
    def apply( sym: String, args: Seq[LambdaExpression] ): LambdaExpression =
      Apps( Const( sym, FunctionType( Ti, args.map( _.exptype ) ) ), args )
    def apply( sym: String, args: LambdaExpression* )( implicit dummyImplicit: DummyImplicit ): LambdaExpression =
      TptpTerm( sym, args )
    def unapplySeq( expr: LambdaExpression ): Option[( String, Seq[LambdaExpression] )] = expr match {
      case Apps( Const( sym, _ ), args ) => Some( ( sym, args ) )
      case _                             => None
    }
  }
  def TptpAtom( sym: String, args: Seq[LambdaExpression] ): HOLAtom =
    ( sym, args ) match {
      case ( "equal", Seq( a, b ) ) => Eq( a, b ) // old tptp syntax
      case _                        => Apps( Const( sym, FunctionType( To, args.map( _.exptype ) ) ), args ).asInstanceOf[HOLAtom]
    }

  object GeneralList {
    val name = "$general_list"
    def apply( elems: Seq[GeneralTerm] ): LambdaExpression = TptpTerm( name, elems )
    def apply( elems: GeneralTerm* )( implicit dummyImplicit: DummyImplicit ): LambdaExpression = TptpTerm( name, elems )
    def unapplySeq( expr: LambdaExpression ): Option[Seq[LambdaExpression]] = expr match {
      case Apps( Const( `name`, _ ), elems ) => Some( elems )
      case _                                 => None
    }
  }
  object GeneralColon {
    val name = "$general_colon"
    def apply( a: GeneralTerm, b: GeneralTerm ): LambdaExpression = TptpTerm( name, a, b )
    def unapplySeq( expr: LambdaExpression ): Option[Seq[LambdaExpression]] = expr match {
      case Apps( Const( `name`, _ ), elems ) => Some( elems )
      case _                                 => None
    }
  }
}
