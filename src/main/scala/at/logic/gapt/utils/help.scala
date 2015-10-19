package at.logic.gapt.utils

import java.nio.file.{ Paths, Files }

/**
 * Created by sebastian on 19.10.15.
 */

/**
 * Opens the scala documentation in a browser window.
 *
 */
object help {

  /**
   *
   * @return The location of the index.html file. Will try the apidocs directory from the tarball, the api directory
   *         from sbt doc and the logic.at website, in that order.
   */
  private def indexPath = {
    val tarballPath = Paths.get( "apidocs", "index.html" ).toAbsolutePath
    val devPath = Paths.get( "target", "scala-2.11", "api", "index.html" ).toAbsolutePath

    if ( Files.exists( tarballPath ) )
      tarballPath.toUri.toString
    else if ( Files.exists( devPath ) )
      devPath.toUri.toString
    else
      "https://logic.at/gapt/api/"
  }

  /**
   * Opens the index of the documentation.
   *
   */
  def apply(): Unit = {
    val pb = new ProcessBuilder( "xdg-open", indexPath )
    val p = pb.start()
    p.waitFor()
  }

  /**
   * Opens the scaladoc page of an object.
   *
   * @param a An object. If it's not of a type defined within gapt, this won't work.
   */
  def apply( a: AnyRef ) {
    val url = indexPath + "#" + a.getClass.getName
    val pb = new ProcessBuilder( "xdg-open", url )
    val p = pb.start()
    p.waitFor()
  }
}
