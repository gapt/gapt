package gapt.utils

import java.net.{HttpURLConnection, URI, URL}
import java.nio.file.{Files, Paths}

/**
 * Opens the scala documentation in a browser window.
 *
 */
object help {
  private val tarballPathBase = Paths.get("apidocs").toAbsolutePath
  private val devPathBase = Paths.get("target", "scala-3.3.1", "unidoc").toAbsolutePath

  private val websitePath = "https://logic.at/gapt/api/"

  private val (indexURI, localDocs, basePath) = {

    if (Files.exists(tarballPathBase))
      (tarballPathBase.toUri.toString, true, Some(tarballPathBase))
    else if (Files.exists(devPathBase))
      (devPathBase.toUri.toString, true, Some(devPathBase))
    else
      (websitePath, false, None)
  }

  private def docPageExists(name: String): Boolean = {
    if (localDocs) {
      val classNamePath = (name.replace('.', '/') ++ ".html").split('/')
      val filePath = Paths.get(classNamePath.head, classNamePath.tail: _*)
      val path = basePath.map(p => p.resolve(filePath))
      path.fold(false)(Files.exists(_))
    } else {
      val classNameURL = name.replace('.', '/') ++ ".html"
      val url = new URI(websitePath + classNameURL).toURL
      val huc = url.openConnection().asInstanceOf[HttpURLConnection]
      huc.setRequestMethod("GET")
      huc.connect()
      val code = huc.getResponseCode
      huc.disconnect()

      code != 404
    }
  }

  // open an URL in a cross-platform way
  private def openUrl(url: String): Unit = {
    val command = System.getProperty("os.name") match {
      case os if os.contains("Mac")   => "open"
      case os if os.contains("Linux") => "xdg-open"
      case os                         => throw UnsupportedOperationException(s"cannot open \"$url\" automatically as the gapt help command does not support the operating system \"$os\" at the moment")
    }
    val pb = new ProcessBuilder(command, url)
    val p = pb.start()
    p.waitFor()
  }

  /**
   * Opens the index of the documentation.
   *
   */
  def apply(): Unit = {
    openUrl(indexURI + "index.html")
  }

  /**
   * Opens the scaladoc page of an object.
   *
   * @param a An object. If it's not of a type defined within gapt, this won't work.
   */
  def apply(a: AnyRef): Unit = {
    val className_ = a.getClass.getName
    val (className, objectName) = if (className_ endsWith "$") {
      (className_.init, className_)
    } else {
      (className_, className_ ++ "$")
    }
    val finalName =
      if (docPageExists(className))
        className
      else
        objectName
    val url = indexURI + finalName.replace(".", "/") + ".html"
    println(url)
    openUrl(url)
  }
}
