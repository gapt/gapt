package at.logic.gapt.utils

import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes

object glob {
  private val dirAndRest = """([^*?\[]*/)(.*)""".r

  def paths( pattern: String ): Seq[Path] = {
    val ( dir, rest ) = pattern match {
      case dirAndRest( d, r ) => ( d, r )
      case _                  => ( ".", pattern )
    }
    val pathMatcher = FileSystems.getDefault.getPathMatcher( s"glob:$rest" )

    val res = Seq.newBuilder[Path]
    Files.walkFileTree( Paths get dir, new SimpleFileVisitor[Path] {
      override def visitFile( file: Path, attrs: BasicFileAttributes ): FileVisitResult = {
        if ( pathMatcher matches file )
          res += file
        FileVisitResult.CONTINUE
      }
    } )
    res.result()
  }

  def apply( pattern: String ): Seq[String] = paths( pattern ).map( _.normalize.toString )
}
