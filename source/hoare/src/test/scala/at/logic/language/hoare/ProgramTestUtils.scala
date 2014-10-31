package at.logic.language.hoare

import at.logic.language.fol.{FOLFormula, FOLTerm}
import at.logic.parsing.hoare.SimpleProgramParser
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.parsing.readers.StringReader

trait ProgramTestUtils {
  private class MyFOLParser(input: String) extends StringReader(input) with SimpleFOLParser

  def program(s: String) = SimpleProgramParser.parseProgram(s)

  def formula(s: String) = new MyFOLParser(s).getTerm().asInstanceOf[FOLFormula]

  def term(s: String) = new MyFOLParser(s).getTerm().asInstanceOf[FOLTerm]
}
