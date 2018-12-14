package gapt.utils

import java.io.IOException

import scala.concurrent._
import scala.concurrent.duration._
import gapt.formats.InputFile

object runProcess {

  def withTempInputFile( cmd: Seq[String], input: String, catchStderr: Boolean = false ): String =
    withTempFile.fromString( input ) { tempFile =>
      apply( cmd :+ tempFile.toString, "", catchStderr )
    }

  def apply( cmd: Seq[String], stdin: String = "", catchStderr: Boolean = false ): String =
    withExitValue( cmd, stdin, catchStderr ) match {
      case ( 0, out )         => out
      case ( exitValue, out ) => throw new IOException( s"${cmd mkString " "} exited with value $exitValue:\n$out" )
    }

  private implicit val newThreadExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor( runnable => new Thread( runnable ).start() )

  def withExitValue( cmd: Seq[String], stdin: String = "", catchStderr: Boolean = false ): ( Int, String ) = {
    val pb = new ProcessBuilder( cmd: _* )

    if ( catchStderr ) pb.redirectErrorStream( true )

    val p = pb.start()

    val shutdownHook = new Thread { override def run() = p.destroy() }
    Runtime.getRuntime.addShutdownHook( shutdownHook )

    try {
      val stdout = Future( InputFile.readStream( p.getInputStream ) )

      blocking {
        p.getOutputStream.write( stdin getBytes )
        p.getOutputStream.close()

        val exitValue = p.waitFor()

        exitValue -> Await.result( stdout, Duration.Inf )
      }
    } finally {
      p.destroy()
      Runtime.getRuntime.removeShutdownHook( shutdownHook )
    }
  }

}
