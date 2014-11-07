package at.logic.parsing.shlk

import at.logic.language.hol.{Formula, HOLVar, HOLFormula, HOLExpression}
import at.logic.language.lambda.types.{To, FunctionType, Tindex}
import at.logic.language.schema._
import at.logic.parsing.language.HOLParser

import scala.util.matching.Regex
import scala.util.parsing.combinator.Parsers

abstract trait HLKFormulaParser extends Parsers {
  //abstract parsers for formulas
  def term: Parser[HOLExpression];
  def formula: Parser[HOLFormula];
  def variable: Parser[HOLVar];

}

trait SchemaFormulaParser extends HLKFormulaParser with HOLParser {

  def goal = term

  var predicate_arities = Map.empty[String, Int]

  def intConst : Parser[IntegerTerm] = "[0-9]+".r ^^ { x => intToTerm(x.toInt) }
  def intVar: Parser[IntVar] = "[ijmnkx]".r ^^ { x => IntVar(x) }

  def term: Parser[SchemaExpression] = ( non_formula | formula)
  def formula: Parser[SchemaFormula] = (atom | neg | big | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[SchemaFormula]}
  def intTerm: Parser[SchemaExpression] = index //| schemaFormula
  def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )


  def intToTerm(i : Int) : IntegerTerm = {
    require(i >= 0, "Can only process positive integer constants")
    if (i == 0)
      IntZero()
    else
      Succ(intToTerm(i-1))
  }


  private def add(x: IntegerTerm, y:IntegerTerm) : IntegerTerm = y match {
    case IntZero() => x
    case Succ(y_) => add(Succ(x), y_)
    case IntVar(v) => throw new Exception("Sum calculation during parsing requires the second parameter to be ground, encountered: "+y)
    case _ => throw new Exception("Unhandled integer term in sum calculation: "+y)
  }

  private def sum : Parser[IntegerTerm] = intVar ~ ("+" ~> intConst) ^^ {case v ~ c => add(v,c) }

  private def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
    case "s(" ~ intTerm ~ ")" => Succ(intTerm.asInstanceOf[IntegerTerm])
  }

  def schemaFormula = formula

  def indPred : Parser[SchemaFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep(index,",") ~ ")" ^^ {
    case x ~ "(" ~ l ~ ")" => {
      if (! predicate_arities.isDefinedAt(x.toString) )
      {
        predicate_arities = predicate_arities + ((x.toString, l.size))
        predicate_arities
      }
      else if (predicate_arities.get(x.toString).get != l.size ) {
        throw new Exception("Input ERROR : Indexed Predicate '"+x.toString+"' should have arity "+predicate_arities.get(x.toString).get+ ", but not "+l.size+" !")
      }

      IndexedPredicate(x, l)
    }
  }

  def big : Parser[SchemaFormula] = rep1(prefix) ~ schemaFormula ^^ {
    case l ~ schemaFormula  => {
      l.reverse.foldLeft(schemaFormula.asInstanceOf[SchemaFormula])((res, triple) => {
        if (triple._1)
          BigAnd(triple._2, res, triple._3, triple._4)
        else
          BigOr(triple._2, res, triple._3, triple._4)
      })
    }
  }
  def non_formula: Parser[SchemaExpression] = (fo_term | s_term | indexedVar | abs | variable | constant | var_func | const_func)
  def s_term: Parser[SchemaExpression] = "[g,h]".r ~ "(" ~ intTerm ~ "," ~ non_formula ~ ")" ^^ {
    case name ~ "(" ~ i ~ "," ~ args ~ ")" => {
      sTerm(name, i.asInstanceOf[SchemaExpression], args.asInstanceOf[SchemaExpression]::Nil)
    }
  }


  private def fo_term: Parser[SchemaExpression] = "[f]".r ~ "(" ~ non_formula ~ ")" ^^ {
    case name ~ "(" ~ arg ~ ")" => {
      foTerm(name, arg.asInstanceOf[SchemaExpression]::Nil)
    }
  }
  def indexedVar: Parser[SchemaVar] = regex(new Regex("[z]")) ~ "(" ~ intTerm ~ ")" ^^ {
    case x ~ "(" ~ index ~ ")" => {
      indexedFOVar(x, index.asInstanceOf[IntegerTerm])
    }
  }

  def variable: Parser[SchemaVar] = (indexedVar | FOVariable)//regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), i->i).asInstanceOf[SchemaVar]}
  private def FOVariable: Parser[SchemaVar] = regex(new Regex("[xya]" + word))  ^^ {case x => foVar(x)}
  private def constant: Parser[SchemaConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => SchemaConst(x, Tindex->Tindex)}
  private def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
  private def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
  private def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
  private def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => SchemaAbs(v,x)}
  private def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
  private def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom)
  private def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
  private def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
  private def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
    Atom(SchemaVar(x, FunctionType(To, params.map(_.exptype))), params)
  }}

  //      def const_atom: Parser[SchemaFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
  def const_atom: Parser[SchemaFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {

    Atom(SchemaConst(x, FunctionType(To, params.map(_.exptype))), params)
  }}
  //def equality: Parser[SchemaFormula] = eq_infix | eq_prefix // infix is problematic in higher order
  def equality: Parser[SchemaFormula] = eq_prefix // infix is problematic in higher order
  def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
  def var_func: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  =>
    Function(SchemaVar(x, FunctionType(Tindex, params.map(_.exptype))), params)}
  def const_func: Parser[SchemaExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  =>
    Function(SchemaConst(x, FunctionType(Tindex, params.map(_.exptype))), params)}

  protected def word: String = """[a-zA-Z0-9$_{}]*"""
  protected def symbol: Parser[String] = symbols.r
  def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // *+-/\^<>=`~?@&|!#{}';

  // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
  def prefix : Parser[Tuple4[Boolean, IntVar, IntegerTerm, IntegerTerm]] = """[BigAnd]*[BigOr]*""".r ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
    case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
      Tuple4(true, intVar1, ind1, ind2)
    }
    case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
      Tuple4(false, intVar1, ind1, ind2)
    }
  }

}
