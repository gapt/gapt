import java.io._
import scala.io.Source

/**********
 * test script for prover9 import, usage example from CLI:
 *
 * scala> :load ../testing/testProver9Import.scala
 * scala> testProver9Import( "../testing/prover9-TSTP/ALG/", 5 )
 **********/

/**
 * A wrapper around file, allowing iteration either on direct children or on directory tree
 **/
class MyFile(file: File) {

  def children = new Iterable[File] {
    def iterator = if (file.isDirectory) file.listFiles.iterator else Iterator.empty
  }

  def andTree : Iterable[File] =
    Seq(file) ++ children.flatMap(child => new MyFile(child).andTree)
}

/**
 * takes a directory name and a timeout (in seconds) as argument,
 * processes all .out-files below the given directory
 **/
object testProver9Import {
  def apply( dir: String, to: Long  ) {
    println( "Testing ivy-import with timeout " + to + "s:" )
    var n_total = 0
    var n_OK = 0
    var list_failure = List[String]()
    
    val root = new MyFile( new File( dir ) )

    for ( file <- root.andTree if file.getName.endsWith( ".out" ) ) {
      n_total += 1
      print( "  " + file.getName() + " " )

      val suc_import = runWithTimeout( to * 1000 ) {
        loadProver9LKProof( file.getCanonicalPath() )
      }
      if ( suc_import == None ) {
        println( "[ FAIL ]" )
        list_failure = file.getCanonicalPath() :: list_failure
      }
      else {
        n_OK += 1
        println ("[ OK ]" )
      }
    }

    println( "\nTotal Stats: " + n_OK + "/" + n_total + " OK" )
    println( "Failures:" )
    list_failure.foreach( e => println( "  " + e ) )
  }

  /**
   * Run f
   *
   * If f terminates within to milliseconds return its result, if it throws an
   * exception or does not terminate within to milliseconds, return None.
   **/
  private def runWithTimeout[T]( to: Long )( f: => T ) : Option[T] = {    
    var output:Option[T] = None

    val r = new Runnable { def run() { try { output = Some( f ) } catch { case ex: Exception => output = None } } }
    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) t.stop()

    output
  }
}
