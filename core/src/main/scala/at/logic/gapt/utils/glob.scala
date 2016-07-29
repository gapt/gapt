package at.logic.gapt.utils

import better.files._

object glob {
  private val dirAndRest = """([^*?\[]*/)(.*)""".r

  @deprecated( """Use file"some/path".glob("**/*.s") instead.""", "2.3" )
  def apply( pattern: String ): Seq[String] = {
    val ( dir, rest ) = pattern match {
      case dirAndRest( d, r ) => ( d, r )
      case _                  => ( ".", pattern )
    }

    dir.toFile.glob( rest ).map( _.pathAsString ).toSeq
  }
}
