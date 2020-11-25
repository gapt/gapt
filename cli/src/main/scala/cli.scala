package gapt

package object cli {

  val welcomeMessage: String =
    """
    |*************************************
    |*    Welcome to the GAPT shell!     *
    |*************************************
    |
    |Copyright (C) 2009-2019  GAPT developers
    |
    |This program comes with ABSOLUTELY NO WARRANTY. This is free
    |software, and you are welcome to redistribute it under certain
    |conditions; type `copying' for details.
    |""".stripMargin

  val predefFileName: String = "gapt-cli-prelude.scala"

}
