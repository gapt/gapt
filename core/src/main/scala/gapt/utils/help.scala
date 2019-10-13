package gapt.utils

import java.net.{ HttpURLConnection, URL }
import java.nio.file.{ Files, Paths }

/**
 * Opens the scala documentation in a browser window.
 *
 */
object help {
  private val tarballPathBase = Paths.get( "apidocs" ).toAbsolutePath
  private val devPathBase = Paths.get( "target", "scala-2.12", "unidoc" ).toAbsolutePath

  private val websitePath = "https://logic.at/gapt/api/"

  private val ( indexURI, localDocs, basePath ) = {

    if ( Files.exists( tarballPathBase ) )
      ( tarballPathBase.toUri.toString, true, Some( tarballPathBase ) )
    else if ( Files.exists( devPathBase ) )
      ( devPathBase.toUri.toString, true, Some( devPathBase ) )
    else
      ( websitePath, false, None )
  }

  private def docPageExists( name: String ): Boolean = {
    if ( localDocs ) {
      val classNamePath = ( name.replace( '.', '/' ) ++ ".html" ).split( '/' )
      val filePath = Paths.get( classNamePath.head, classNamePath.tail: _* )
      val path = basePath.map( p => p.resolve( filePath ) )
      path.fold( false )( Files.exists( _ ) )
    } else {
      val classNameURL = name.replace( '.', '/' ) ++ ".html"
      val url = new URL( websitePath + classNameURL )
      val huc = url.openConnection().asInstanceOf[HttpURLConnection]
      huc.setRequestMethod( "GET" )
      huc.connect()
      val code = huc.getResponseCode
      huc.disconnect()

      code != 404
    }
  }

  /**
   * Opens the index of the documentation.
   *
   */
  def apply(): Unit = {
    val pb = new ProcessBuilder( "xdg-open", indexURI )
    val p = pb.start()
    p.waitFor()
  }

  /**
   * Opens the scaladoc page of an object.
   *
   * @param a An object. If it's not of a type defined within gapt, this won't work.
   */
  def apply( a: AnyRef ): Unit = {
    val className_ = a.getClass.getName
    val ( className, objectName ) = if ( className_ endsWith "$" ) {
      ( className_.init, className_ )
    } else {
      ( className_, className_ ++ "$" )
    }
    val finalName =
      if ( docPageExists( className ) )
        className
      else
        objectName
    val url = indexURI + finalName.replace( ".", "/" ) + ".html"
    println( url )
    val pb = new ProcessBuilder( "xdg-open", url )
    val p = pb.start()
    p.waitFor()
  }
}
