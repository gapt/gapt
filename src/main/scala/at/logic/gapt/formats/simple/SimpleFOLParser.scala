/*
 * HOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.formats.simple

import at.logic.gapt.expr._

import scala.util.matching.Regex

trait SimpleFOLParser extends SimpleHOLParser {
  override def goal = term

  override def term: Parser[LambdaExpression] = ( formula | non_formula )
  override def formula: Parser[Formula] = ( and | or | imp | neg | forall | exists | const_atom ) ^? { case trm: FOLFormula => trm.asInstanceOf[FOLFormula] }
  override def non_formula: Parser[LambdaExpression] = ( const_func | variable | constant ) ^? { case trm: FOLTerm => trm }

  override def variable: Parser[Var] = regex( new Regex( "[u-z]" + word ) ) ^^ {
    case x => FOLVar( x )
  }
  override def constant: Parser[Const] = regex( new Regex( "[a-t]" + word ) ) ^^ {
    case x => FOLConst( x )
  }

  override def const_atom: Parser[Formula] = equation | const_atom1 | const_atom2
  def equation: Parser[Formula] = "=(" ~ repsep( non_formula, "," ) ~ ")" ^^ { case "=(" ~ params ~ ")" if params.size == 2 => Eq( params( 0 ).asInstanceOf[FOLTerm], params( 1 ).asInstanceOf[FOLTerm] ) }
  def const_atom1: Parser[Formula] = regex( new Regex( "[" + symbols + "A-Z]" + word ) ) ~ "(" ~ repsep( non_formula, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => FOLAtom( x, params.asInstanceOf[List[FOLTerm]] )
  }
  def const_atom2: Parser[Formula] = regex( new Regex( "[" + symbols + "A-Z]" + word ) ) ^^ {
    case x => FOLAtom( x, Nil )
  }
  override def const_func: Parser[LambdaExpression] = regex( new Regex( "[" + symbols + "a-z]" + word ) ) ~ "(" ~ repsep( non_formula, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => FOLFunction( x, params.asInstanceOf[List[FOLTerm]] )
  }

  override def and: Parser[Formula] = "And" ~ formula ~ formula ^^ { case "And" ~ x ~ y => And( x.asInstanceOf[FOLFormula], y.asInstanceOf[FOLFormula] ) }
  override def or: Parser[Formula] = "Or" ~ formula ~ formula ^^ { case "Or" ~ x ~ y => Or( x.asInstanceOf[FOLFormula], y.asInstanceOf[FOLFormula] ) }
  override def imp: Parser[Formula] = "Imp" ~ formula ~ formula ^^ { case "Imp" ~ x ~ y => Imp( x.asInstanceOf[FOLFormula], y.asInstanceOf[FOLFormula] ) }
  override def neg: Parser[Formula] = "Neg" ~ formula ^^ { case "Neg" ~ x => Neg( x.asInstanceOf[FOLFormula] ) }
  override def atom: Parser[Formula] = ( equality | var_atom | const_atom )
  override def forall: Parser[Formula] = "Forall" ~ variable ~ formula ^^ { case "Forall" ~ v ~ x => All( v.asInstanceOf[FOLVar], x.asInstanceOf[FOLFormula] ) }
  override def exists: Parser[Formula] = "Exists" ~ variable ~ formula ^^ { case "Exists" ~ v ~ x => Ex( v.asInstanceOf[FOLVar], x.asInstanceOf[FOLFormula] ) }
}

