/*
 * HOLExpressionArithmeticalExporter.scala
 *
 */

package at.logic.parsing.language.arithmetic

import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.symbols.SymbolA
import at.logic.language.schema.{TopC, BottomC, BigAnd, BigOr, SchemaFormula}
import at.logic.language.schema.logicSymbols.BiggerThanSymbol
import at.logic.parsing.OutputExporter
import at.logic.parsing.language.HOLTermExporter

// FIXME: bad import, we don't want to import
// something from transformations here.
import at.logic.transformations.ceres.struct.ClauseSetSymbol
import at.logic.transformations.ceres.struct.TypeSynonyms.CutConfiguration


trait HOLTermArithmeticalExporter extends OutputExporter with HOLTermExporter {
  def exportFunction(t: HOLExpression): Unit = t match {
    case TopC => getOutput.write("\\top")
    case BottomC => getOutput.write("\\bot")
    case Function(HOLConst("+",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" + "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("-",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" - "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("*",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(" * "); exportTerm(y); getOutput.write(")")}
    case Function(HOLConst("""/""",_), x::y::Nil, _) => {getOutput.write("("); exportTerm(x); getOutput.write(""" / """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst("<",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" < """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst(">",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" > """); exportTerm(y); getOutput.write(")")}
    case Atom(HOLConst("=",_), x::y::Nil) => {getOutput.write("("); exportTerm(x); getOutput.write(""" = """); exportTerm(y); getOutput.write(")")}
    case BigAnd(v, f, s, e) =>
      getOutput.write("(")
      getOutput.write("""\bigwedge_{""")
      exportTerm(v)
      getOutput.write(" = ")
      exportTerm(s)
      getOutput.write("}^{")
      exportTerm(e)
      getOutput.write("}")
      exportTerm(f)
      getOutput.write(")")

    case BigOr(v, f, s, e) =>
      getOutput.write("(")
      getOutput.write("""\bigvee_{""")
      exportTerm(v)
      getOutput.write(" = ")
      exportTerm(s)
      getOutput.write("}^{")
      exportTerm(e)
      getOutput.write("}")
      exportTerm(f)
      getOutput.write(")")

    case Function(VarOrConst(name,_), args, _) => {
      getOutput.write(name)
      getOutput.write("(")
      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})
      getOutput.write(")")
  }
    case Atom(c, args) => {
      val sym = c match {
        case h@HOLConst(_,_) => h.asInstanceOf[HOLConst].sym
        case h@HOLConst(_,_) => h.asInstanceOf[HOLVar].sym
      }

      var nonschematic = sym match {
        case cs : ClauseSetSymbol => {
          getOutput.write("CL^{(");

          writeCutConf(cs.cut_occs);
          getOutput.write("),");
          getOutput.write(cs.name);
          getOutput.write("}_{");
          getOutput.write("{");
          false;
        }
        case _ =>
          getOutput.write(sym.toString)
          true
      }
      if(nonschematic) {
        getOutput.write("(")
        getOutput.write("{")
      }

      if (args.size > 0) exportTerm(args.head)
      if (args.size > 1) args.tail.foreach(x => {getOutput.write(","); exportTerm(x)})

      if(nonschematic){
        getOutput.write(")}")
      }
      else
        getOutput.write("}}")
    }
  }

  def exportSymbol(sym: SymbolA): Unit = sym match {
    case cs : ClauseSetSymbol =>
      getOutput.write("CL^{("); writeCutConf(cs.cut_occs);
      getOutput.write("),");
      getOutput.write(cs.name);
      getOutput.write("}")
    case _ => getOutput.write(sym.toString)
  }

  private def writeCutConf( cc: CutConfiguration) = {
    if(cc._1.size > 0) {
      exportTerm( cc._1.head );
      cc._1.tail.foreach ( f => {getOutput.write(", "); exportTerm( f ) })
    }
    getOutput.write("|")
    if(cc._2.size > 0) {
      exportTerm( cc._2.head )
      cc._2.tail.foreach ( f => {getOutput.write(", "); exportTerm( f ) })
    }
  }
}
