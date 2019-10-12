package gapt.cli

import ammonite.ops.{ Path, pwd, read }
import gapt.cli.CLIMain.{ ScriptsResultHolder }
import gapt.examples.Script
import gapt.formats.ClasspathInputFile

import scala.tools.nsc.Settings
import scala.tools.nsc.interpreter.IMain

object GaptScriptInterpreter {

  private val settings = new Settings
  settings.usejavacp.value = true
  settings.language.value = {
    import settings.language.domain._
    ValueSet( postfixOps, implicitConversions )
  }
  settings.feature.value = true
  settings.deprecation.value = true

  def run( scriptFileName: String, scriptArguments: Seq[String] ): Unit = {
    val predefCode: String = readPredefFile
    // Strip package declaration, the script compiler doesn't like it.
    val packageRegex = """(?s)package [A-Za-z.]+\n(.*)""".r
    val scriptSrc = read( Path( scriptFileName, pwd ) ) match {
      case packageRegex( restOfScript ) => restOfScript
      case scriptWithoutPackage         => scriptWithoutPackage
    }

    val interpreter = new IMain( settings )
    interpreter.beQuietDuring {
      interpreter.interpret( predefCode + scriptSrc )

      val scriptsName = interpreter.naming.freshUserTermName()
      val scripts = new ScriptsResultHolder
      interpreter.bind( scriptsName.toString, scripts )

      // Execute all defined objects of type Script.
      // TODO(gabriel): use reflection again
      for {
        defTerm <- interpreter.namedDefinedTerms
        if interpreter.typeOfTerm( defTerm.toString ) <:< interpreter.global.typeOf[Script]
      } interpreter.interpret( s"$scriptsName.add($defTerm)\n" )

      for ( script <- scripts.result )
        script.main( scriptArguments.toArray )
    }
  }

  private def readPredefFile: String =
    ClasspathInputFile( predefFileName ).read
}
