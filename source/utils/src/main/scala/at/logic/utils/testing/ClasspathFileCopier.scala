package at.logic.utils.testing

import java.io.File
import java.nio.file.Files
import java.nio.file.StandardCopyOption._

/**
 * Copy resources from the classpath as actual files into the temporary directory.
 */
trait ClasspathFileCopier {
  private val basenameExtRegex = """(?:^|.*/)([^/]+)\.([^./]+)""".r

  /**
   * Creates a temporary copy of a resource in the classpath.  This temporary
   * copy is automatically deleted on program termination.
   *
   * @param path Path of the resource, e.g. "test.xml" if the resource is located in
   *             "project/src/test/resources/test.xml" in the source tree.
   * @return Path to the temporary copy.
   */
  def tempCopyOfClasspathFile(path: String): String = {
    val (basename, ext) = path match {
      case basenameExtRegex(basename, ext) => (basename, ext)
      case _ => ("copyFileFromBasename", "tmp")
    }
    val tempFile = File.createTempFile(basename, ext)
    Files.copy(getClass.getClassLoader.getResourceAsStream(path), tempFile.toPath, REPLACE_EXISTING)
    tempFile.getPath
  }
}
