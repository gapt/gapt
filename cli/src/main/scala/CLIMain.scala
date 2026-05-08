package gapt.cli

object CLIMain {

  def main(args: Array[String]): Unit = {

    args match {

      // If invoked as ./gapt.sh `script`, then execute `script` and exit.
      case Array(scriptFile, scriptArgs @ _*) =>
        GaptScriptInterpreter.run(scriptFile, scriptArgs)

      case _ =>
        GaptRepl().run()
    }
  }

}
