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

class MyOption[+T >: Nothing]
case object MyNone extends MyOption[Nothing]
case class MyException[+T >: Nothing](exp: Exception) extends MyOption[T]
case class MySome[+T >:Nothing](value: T) extends MyOption[T]

/**
 * takes a directory name and a timeout (in seconds) as argument,
 * processes all .out-files below the given directory
 **/
object testProver9Import {

  type MyMap = scala.collection.mutable.Map[String,List[Pair[String,Option[Exception]]]]

  def apply( dir: String, to: Long  ) {
    println( "Testing prover9-import with timeout " + to + "s:" )
    var n_total = 0
    var n_exp = 0
    var n_none = 0
    var n_OK = 0

    var list_succ = List[String]()
    val map_failure = scala.collection.mutable.Map[String,List[Pair[String,Option[Exception]]]]()

    def addOrUpdate(map: MyMap, err: String, value: String, ex: Option[Exception]) = {
      try {
        val ls = map(err)
        map(err) = (value,ex) :: ls
      } catch {
        case nsee: NoSuchElementException =>  map(err) = List((value,ex))
      }

    }

    val root = new MyFile( new File( dir ) )

    for ( file <- root.andTree if file.getName.endsWith( ".out" ) ) {
      n_total += 1
      print( "  " + file.getName() + " " )

      val suc_import = runWithTimeout( to * 1000 ) {
        loadProver9LKProof( file.getCanonicalPath() )
      }
      suc_import match {
        case MyNone => {
          println( "[ FAIL ]" )
          addOrUpdate(map_failure, "None", file.getCanonicalPath(), None)
        }
        case MyException(ex) => {
          println( "[ FAIL " + ex.getClass.getName + " ]")
          addOrUpdate(map_failure, ex.getClass.getName,file.getCanonicalPath(), Some(ex))
        }
        case _ => {
          n_OK += 1
          println ("[ OK ]" )
          list_succ = file.getCanonicalPath() :: list_succ
        }
      }
    }

    println( "\nTotal Stats: " + n_OK + "/" + n_total + " OK" )
    println( "Successes:" )
    list_succ.foreach( e => println ( "  " + e ) )
    println( "Failures:" )
    map_failure.keySet.foreach( e => println( "  " + e + " -> " + map_failure(e).size))
    map_failure.values.flatMap(x => x).foreach( e => {println( "  " + e._1); (e._2 match {case None => (); case Some(ex) => ex.printStackTrace})})
  }

  /**
   * Run f
   *
   * If f terminates within to milliseconds return its result, if it throws an
   * exception or does not terminate within to milliseconds, return None.
   **/
  private def runWithTimeout[T >: Nothing]( to: Long )( f: => T ) : MyOption[T] = {
    var output:MyOption[T] = MyNone

    val r = new Runnable { def run() { try { output = MySome( f ) } catch { case ex: Exception => output = MyException(ex) } } }
    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) t.stop()

    output
  }
}
